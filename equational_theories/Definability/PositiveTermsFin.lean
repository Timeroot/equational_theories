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

/-- Equation 125 `x = y ◇ ((y ◇ x) ◇ y)` is term-definable from equation 63 `x = y ◇ (x ◇ (x ◇ y))`
over finite magmas, via the term `x □ y := y ◇ (y ◇ x)`. -/
private theorem aux63_125 [Finite G] [Magma G] (h : Equation63 G) (x y : G) :
    x = (y ◇ (y ◇ (x ◇ (x ◇ y)))) ◇ ((y ◇ (y ◇ (x ◇ (x ◇ y)))) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef8 : x ≠ (y ◇ (y ◇ (x ◇ (x ◇ y)))) ◇ ((y ◇ (y ◇ (x ◇ (x ◇ y)))) ◇ y) := mod_symm nh
  have ef11 : x ≠ (y ◇ x) ◇ ((y ◇ x) ◇ y) := by
    first | exact superpose ef6 ef8 | exact superpose ef8 ef6
  subsumption ef11 ef7

theorem Equation125_termDefinableFromFin_Equation63 : Law125.TermDefinableFromFin Law63 := by
  intro G _ M hGL
  have h : Equation63 G := Law63.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op y x))⟩, ?_, ?_⟩
  · rw [@Law125.models_iff]
    exact fun x y ↦ @aux63_125 G _ M h x y
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), rfl⟩

/-- Equation 1692 `x = (y ◇ x) ◇ ((y ◇ x) ◇ y)` is term-definable from equation 63
`x = y ◇ (x ◇ (x ◇ y))` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux63_1692 [Finite G] [Magma G] (h : Equation63 G) (x y : G) :
    x = (y ◇ x) ◇ ((y ◇ x) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef8 : x ≠ (y ◇ x) ◇ ((y ◇ x) ◇ y) := mod_symm nh
  have ef15 : x ≠ x := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  exact absurd rfl ef15

theorem Equation1692_termDefinableFromFin_Equation63 : Law1692.TermDefinableFromFin Law63 := by
  intro G _ M hGL
  have h : Equation63 G := Law63.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law1692.models_iff]
    exact fun x y ↦ @aux63_1692 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

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

/-- Equation 118 `x = y ◇ ((x ◇ y) ◇ y)` is term-definable from equation 73 `x = y ◇ (y ◇ (x ◇ y))`
over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux73_118 [Finite G] [Magma G] (h : Equation73 G) (x y : G) :
    x = (y ◇ (y ◇ x)) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 : x ≠ (y ◇ (y ◇ x)) ◇ y := mod_symm nh
  have ef14 : x ≠ x := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  exact absurd rfl ef14

theorem Equation118_termDefinableFromFin_Equation73 : Law118.TermDefinableFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law118.models_iff]
    exact fun x y ↦ @aux73_118 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 125 `x = y ◇ ((y ◇ x) ◇ y)` is term-definable from equation 73 `x = y ◇ (y ◇ (x ◇ y))`
over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux73_125 [Finite G] [Magma G] (h : Equation73 G) (x y : G) :
    x = y ◇ ((y ◇ x) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 : x ≠ y ◇ ((y ◇ x) ◇ y) := mod_symm nh
  have ef16 : x ≠ x := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  exact absurd rfl ef16

theorem Equation125_termDefinableFromFin_Equation73 : Law125.TermDefinableFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law125.models_iff]
    exact fun x y ↦ @aux73_125 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

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

/-- Equation 1692 `x = (y ◇ x) ◇ ((y ◇ x) ◇ y)` is term-definable from equation 73
`x = y ◇ (y ◇ (x ◇ y))` over finite magmas, via the term `x □ y := (x ◇ y) ◇ x`. -/
private theorem aux73_1692 [Finite G] [Magma G] (h : Equation73 G) (x y : G) :
    x = (((y ◇ x) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇ ((y ◇ x) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      x ≠ (((y ◇ x) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇ ((y ◇ x) ◇ y) := mod_symm nh
  have ef16 : x ≠ y ◇ ((y ◇ x) ◇ y) := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  subsumption ef16 ef9

theorem Equation1692_termDefinableFromFin_Equation73 : Law1692.TermDefinableFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_⟩
  · rw [@Law1692.models_iff]
    exact fun x y ↦ @aux73_1692 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩

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

/-- Equation 880 `x = y ◇ ((x ◇ y) ◇ (x ◇ y))` is term-definable from equation 115
`x = y ◇ ((x ◇ x) ◇ y)` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux115_880 [Finite G] [Magma G] (h : Equation115 G) (x y : G) :
    x = ((y ◇ x) ◇ (y ◇ x)) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef10 : x ≠ ((y ◇ x) ◇ (y ◇ x)) ◇ y := mod_symm nh
  have ef13 : x ≠ x := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  exact absurd rfl ef13

theorem Equation880_termDefinableFromFin_Equation115 : Law880.TermDefinableFromFin Law115 := by
  intro G _ M hGL
  have h : Equation115 G := Law115.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law880.models_iff]
    exact fun x y ↦ @aux115_880 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` is term-definable from equation 115
`x = y ◇ ((x ◇ x) ◇ y)` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux115_4273 [Finite G] [Magma G] (h : Equation115 G) (x y : G) :
    x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : X1 ◇ ((X0 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef10 : x ◇ (x ◇ x) ≠ y ◇ (x ◇ y) := mod_symm nh
  have ef15 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = X2 ◇ (X0 ◇ X2) := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef54 (X0 : G) : x ◇ (x ◇ x) ≠ X0 ◇ (x ◇ X0) := by
    first | exact superpose ef15 ef10 | exact superpose ef10 ef15
  subsumption ef54 ef15

theorem Equation4273_termDefinableFromFin_Equation115 : Law4273.TermDefinableFromFin Law115 := by
  intro G _ M hGL
  have h : Equation115 G := Law115.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law4273.models_iff]
    exact fun x y ↦ @aux115_4273 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

/-- Equation 63 `x = y ◇ (x ◇ (x ◇ y))` is term-definable from equation 118 `x = y ◇ ((x ◇ y) ◇ y)`
over finite magmas, via the term `x □ y := (x ◇ y) ◇ x`. -/
private theorem aux118_63 [Finite G] [Magma G] (h : Equation118 G) (x y : G) :
    x = (y ◇ ((x ◇ ((x ◇ y) ◇ x)) ◇ x)) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 : x ≠ (y ◇ ((x ◇ ((x ◇ y) ◇ x)) ◇ x)) ◇ y := mod_symm nh
  have ef14 : x ≠ (y ◇ (x ◇ y)) ◇ y := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  subsumption ef14 ef8

theorem Equation63_termDefinableFromFin_Equation118 : Law63.TermDefinableFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_⟩
  · rw [@Law63.models_iff]
    exact fun x y ↦ @aux118_63 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩

/-- Equation 73 `x = y ◇ (y ◇ (x ◇ y))` is term-definable from equation 118 `x = y ◇ ((x ◇ y) ◇ y)`
over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux118_73 [Finite G] [Magma G] (h : Equation118 G) (x y : G) :
    x = ((y ◇ x) ◇ y) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef10 : x ≠ ((y ◇ x) ◇ y) ◇ y := mod_symm nh
  have ef17 : x ≠ x := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  exact absurd rfl ef17

theorem Equation73_termDefinableFromFin_Equation118 : Law73.TermDefinableFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law73.models_iff]
    exact fun x y ↦ @aux118_73 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 125 `x = y ◇ ((y ◇ x) ◇ y)` is term-definable from equation 118 `x = y ◇ ((x ◇ y) ◇ y)`
over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux118_125 [Finite G] [Magma G] (h : Equation118 G) (x y : G) :
    x = (y ◇ (x ◇ y)) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 : x ≠ (y ◇ (x ◇ y)) ◇ y := mod_symm nh
  have ef14 : x ≠ x := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  exact absurd rfl ef14

theorem Equation125_termDefinableFromFin_Equation118 : Law125.TermDefinableFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law125.models_iff]
    exact fun x y ↦ @aux118_125 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 1685 `x = (y ◇ x) ◇ ((x ◇ y) ◇ y)` is term-definable from equation 118
`x = y ◇ ((x ◇ y) ◇ y)` over finite magmas, via the term `x □ y := (y ◇ x) ◇ y`. -/
private theorem aux118_1685 [Finite G] [Magma G] (h : Equation118 G) (x y : G) :
    x = (((y ◇ ((y ◇ x) ◇ y)) ◇ y) ◇ ((x ◇ y) ◇ x)) ◇ ((y ◇ ((y ◇ x) ◇ y)) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 :
      x ≠ (((y ◇ ((y ◇ x) ◇ y)) ◇ y) ◇ ((x ◇ y) ◇ x)) ◇ ((y ◇ ((y ◇ x) ◇ y)) ◇ y) := mod_symm nh
  have ef13 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := superpose ef8 ef8
  have ef14 : x ≠ ((y ◇ x) ◇ ((x ◇ y) ◇ x)) ◇ (y ◇ x) := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  have ef32 : x ≠ ((y ◇ x) ◇ (x ◇ (y ◇ x))) ◇ (y ◇ x) := by
    first | exact superpose ef13 ef14 | exact superpose ef14 ef13
  subsumption ef32 ef8

theorem Equation1685_termDefinableFromFin_Equation118 : Law1685.TermDefinableFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_⟩
  · rw [@Law1685.models_iff]
    exact fun x y ↦ @aux118_1685 G _ M h x y
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩

/-- Equation 1692 `x = (y ◇ x) ◇ ((y ◇ x) ◇ y)` is term-definable from equation 118
`x = y ◇ ((x ◇ y) ◇ y)` over finite magmas, via the term `x □ y := (x ◇ y) ◇ x`. -/
private theorem aux118_1692 [Finite G] [Magma G] (h : Equation118 G) (x y : G) :
    x = (((y ◇ x) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇ ((y ◇ x) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef10 :
      x ≠ (((y ◇ x) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇ ((y ◇ x) ◇ y) := mod_symm nh
  have ef14 : x ≠ ((y ◇ x) ◇ y) ◇ y := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  subsumption ef14 ef9

theorem Equation1692_termDefinableFromFin_Equation118 : Law1692.TermDefinableFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_⟩
  · rw [@Law1692.models_iff]
    exact fun x y ↦ @aux118_1692 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩

/-- Equation 3548 `x ◇ y = y ◇ ((x ◇ y) ◇ x)` is term-definable from equation 118
`x = y ◇ ((x ◇ y) ◇ y)` over finite magmas, via the term `x □ y := (y ◇ x) ◇ x`. -/
private theorem aux118_3548 [Finite G] [Magma G] (h : Equation118 G) (x y : G) :
    (y ◇ x) ◇ x = (((x ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef9 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef10 : (y ◇ x) ◇ x ≠ (((x ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ y := mod_symm nh
  have ef12 : (y ◇ x) ◇ x ≠ ((y ◇ ((y ◇ x) ◇ x)) ◇ y) ◇ y := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  subsumption ef12 ef9

theorem Equation3548_termDefinableFromFin_Equation118 : Law3548.TermDefinableFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) x)⟩, ?_, ?_⟩
  · rw [@Law3548.models_iff]
    exact fun x y ↦ @aux118_3548 G _ M h x y
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 0)), rfl⟩

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

/-- Equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))` is term-definable from equation 464
`x = y ◇ (x ◇ (x ◇ (x ◇ y)))` over finite magmas, via the term `x □ y := y ◇ (y ◇ (y ◇ x))`. -/
private theorem aux464_714 [Finite G] [Magma G] (h : Equation464 G) (x y : G) :
    x = ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇ ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇
      ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇ y))) ◇ (((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇
      ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇ ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇ y))) ◇
      (((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇
      ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇ ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇ y))) ◇ y)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ ((b ◇ a) ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (z ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ≠ ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇ ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇
      ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇ y))) ◇ (((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇
      ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇ ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇ y))) ◇
      (((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇
      ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇ ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))) ◇ y))) ◇
      y)) := mod_symm nh
  have ef12 :
      x ≠ ((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ y))) ◇
      (((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ y))) ◇
      (((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ y))) ◇ y)) := by
    first | exact superpose ef6 ef8 | exact superpose ef8 ef6
  have ef13 : x ≠ (y ◇ x) ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ y)) := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  subsumption ef13 ef7

theorem Equation714_termDefinableFromFin_Equation464 : Law714.TermDefinableFromFin Law464 := by
  intro G _ M hGL
  have h : Equation464 G := Law464.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op y (M.op y x)))⟩, ?_, ?_⟩
  · rw [@Law714.models_iff]
    exact fun x y ↦ @aux464_714 G _ M h x y
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))), rfl⟩

/-- Equation 1492 `x = (y ◇ x) ◇ (y ◇ (y ◇ y))` is term-definable from equation 477
`x = y ◇ (x ◇ (y ◇ (y ◇ y)))` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux477_1492 [Finite G] [Magma G] (h : Equation477 G) (x y : G) :
    x = (y ◇ x) ◇ (y ◇ (y ◇ y)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef8 : x ≠ (y ◇ x) ◇ (y ◇ (y ◇ y)) := mod_symm nh
  have ef11 : x ≠ x := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  exact absurd rfl ef11

theorem Equation1492_termDefinableFromFin_Equation477 : Law1492.TermDefinableFromFin Law477 := by
  intro G _ M hGL
  have h : Equation477 G := Law477.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law1492.models_iff]
    exact fun x y ↦ @aux477_1492 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

/-- Equation 1519 `x = (y ◇ y) ◇ (x ◇ (y ◇ y))` is term-definable from equation 477
`x = y ◇ (x ◇ (y ◇ (y ◇ y)))` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux477_1519 [Finite G] [Magma G] (h : Equation477 G) (x y : G) :
    x = (y ◇ y) ◇ (x ◇ (y ◇ y)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef8 : x ≠ (y ◇ y) ◇ (x ◇ (y ◇ y)) := mod_symm nh
  have ef9 (X0 X1 : G) :
      X1 ◇ (X1 ◇ X1) = X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose ef7 ef7
  have ef15 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef48 (X0 : G) :
      (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇
      ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    first | exact superpose ef15 ef9 | exact superpose ef9 ef15
  have ef50 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef7 ef48 | exact superpose ef48 ef7
  have ef137 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)) = X1 := by
    first | exact superpose ef50 ef6 | exact superpose ef6 ef50
  have ef199 : x ≠ x := by
    first | exact superpose ef137 ef8 | exact superpose ef8 ef137
  exact absurd rfl ef199

theorem Equation1519_termDefinableFromFin_Equation477 : Law1519.TermDefinableFromFin Law477 := by
  intro G _ M hGL
  have h : Equation477 G := Law477.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law1519.models_iff]
    exact fun x y ↦ @aux477_1519 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

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

/-- Equation 1492 `x = (y ◇ x) ◇ (y ◇ (y ◇ y))` is term-definable from equation 481
`x = y ◇ (x ◇ (y ◇ (z ◇ z)))` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux481_1492 [Finite G] [Magma G] (h : Equation481 G) (x y : G) :
    x = (y ◇ x) ◇ (y ◇ (y ◇ y)) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ a) ◇ (b ◇ (c ◇ c)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (c ◇ c)))
      (fun z ↦ (h z b c).symm) a
  have ef6 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (hrot0 ..)
  have ef8 : x ≠ (y ◇ x) ◇ (y ◇ (y ◇ y)) := mod_symm nh
  have ef10 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := superpose ef6 ef6
  have ef19 (X0 : G) : x ≠ (y ◇ x) ◇ (y ◇ (X0 ◇ X0)) := by
    first | exact superpose ef10 ef8 | exact superpose ef8 ef10
  subsumption ef19 ef7

theorem Equation1492_termDefinableFromFin_Equation481 : Law1492.TermDefinableFromFin Law481 := by
  intro G _ M hGL
  have h : Equation481 G := Law481.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law1492.models_iff]
    exact fun x y ↦ @aux481_1492 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

/-- Equation 1496 `x = (y ◇ x) ◇ (y ◇ (z ◇ z))` is term-definable from equation 481
`x = y ◇ (x ◇ (y ◇ (z ◇ z)))` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux481_1496 [Finite G] [Magma G] (h : Equation481 G) (x y z : G) :
    x = (y ◇ x) ◇ (y ◇ (z ◇ z)) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ a) ◇ (b ◇ (c ◇ c)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (c ◇ c)))
      (fun z ↦ (h z b c).symm) a
  have ef6 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (hrot0 ..)
  have ef8 : x ≠ (y ◇ x) ◇ (y ◇ (z ◇ z)) := mod_symm nh
  have ef10 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := superpose ef6 ef6
  have ef22 (X0 : G) : x ≠ (y ◇ x) ◇ (y ◇ (X0 ◇ X0)) := by
    first | exact superpose ef10 ef8 | exact superpose ef8 ef10
  subsumption ef22 ef7

theorem Equation1496_termDefinableFromFin_Equation481 : Law1496.TermDefinableFromFin Law481 := by
  intro G _ M hGL
  have h : Equation481 G := Law481.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law1496.models_iff]
    exact fun x y z ↦ @aux481_1496 G _ M h x y z
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

/-- Equation 910 `x = y ◇ ((y ◇ x) ◇ (y ◇ y))` is term-definable from equation 504
`x = y ◇ (y ◇ (x ◇ (y ◇ y)))` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux504_910 [Finite G] [Magma G] (h : Equation504 G) (x y : G) :
    x = y ◇ ((y ◇ x) ◇ (y ◇ y)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ b)) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot1 ..)
  have ef10 : x ≠ y ◇ ((y ◇ x) ◇ (y ◇ y)) := mod_symm nh
  have ef15 : x ≠ x := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  exact absurd rfl ef15

theorem Equation910_termDefinableFromFin_Equation504 : Law910.TermDefinableFromFin Law504 := by
  intro G _ M hGL
  have h : Equation504 G := Law504.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law910.models_iff]
    exact fun x y ↦ @aux504_910 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

/-- Equation 1722 `x = (y ◇ y) ◇ ((x ◇ y) ◇ y)` is term-definable from equation 504
`x = y ◇ (y ◇ (x ◇ (y ◇ y)))` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux504_1722 [Finite G] [Magma G] (h : Equation504 G) (x y : G) :
    x = (y ◇ (y ◇ x)) ◇ (y ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef10 : x ≠ (y ◇ (y ◇ x)) ◇ (y ◇ y) := mod_symm nh
  have ef13 : x ≠ x := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  exact absurd rfl ef13

theorem Equation1722_termDefinableFromFin_Equation504 : Law1722.TermDefinableFromFin Law504 := by
  intro G _ M hGL
  have h : Equation504 G := Law504.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law1722.models_iff]
    exact fun x y ↦ @aux504_1722 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

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

/-- Equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))` is term-definable from equation 511
`x = y ◇ (y ◇ (y ◇ (x ◇ y)))` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux511_714 [Finite G] [Magma G] (h : Equation511 G) (x y : G) :
    x = y ◇ (y ◇ ((y ◇ x) ◇ y)) := by
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
  have ef11 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (hrot2 ..)
  have ef12 : x ≠ y ◇ (y ◇ ((y ◇ x) ◇ y)) := mod_symm nh
  have ef30 : x ≠ x := by
    first | exact superpose ef11 ef12 | exact superpose ef12 ef11
  exact absurd rfl ef30

theorem Equation714_termDefinableFromFin_Equation511 : Law714.TermDefinableFromFin Law511 := by
  intro G _ M hGL
  have h : Equation511 G := Law511.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law714.models_iff]
    exact fun x y ↦ @aux511_714 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

/-- Equation 1289 `x = y ◇ (((x ◇ y) ◇ y) ◇ y)` is term-definable from equation 511
`x = y ◇ (y ◇ (y ◇ (x ◇ y)))` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux511_1289 [Finite G] [Magma G] (h : Equation511 G) (x y : G) :
    x = (y ◇ (y ◇ (y ◇ x))) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (b ◇ a))) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ (b ◇ z))) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef12 : x ≠ (y ◇ (y ◇ (y ◇ x))) ◇ y := mod_symm nh
  have ef17 : x ≠ x := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  exact absurd rfl ef17

theorem Equation1289_termDefinableFromFin_Equation511 : Law1289.TermDefinableFromFin Law511 := by
  intro G _ M hGL
  have h : Equation511 G := Law511.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law1289.models_iff]
    exact fun x y ↦ @aux511_1289 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 1695 `x = (y ◇ x) ◇ ((y ◇ y) ◇ y)` is term-definable from equation 680
`x = y ◇ (x ◇ ((y ◇ y) ◇ y))` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux680_1695 [Finite G] [Magma G] (h : Equation680 G) (x y : G) :
    x = (y ◇ x) ◇ ((y ◇ y) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ b) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ ((b ◇ b) ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef8 : x ≠ (y ◇ x) ◇ ((y ◇ y) ◇ y) := mod_symm nh
  have ef11 : x ≠ x := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  exact absurd rfl ef11

theorem Equation1695_termDefinableFromFin_Equation680 : Law1695.TermDefinableFromFin Law680 := by
  intro G _ M hGL
  have h : Equation680 G := Law680.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law1695.models_iff]
    exact fun x y ↦ @aux680_1695 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

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

/-- Equation 1316 `x = y ◇ (((y ◇ x) ◇ y) ◇ y)` is term-definable from equation 707
`x = y ◇ (y ◇ ((x ◇ y) ◇ y))` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux707_1316 [Finite G] [Magma G] (h : Equation707 G) (x y : G) :
    x = y ◇ (((y ◇ x) ◇ y) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (a ◇ b))) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ (z ◇ b))) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ (b ◇ a)) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have hrot2 (a b : G) : b ◇ (((b ◇ a) ◇ b) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ ((b ◇ z) ◇ b) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot1 z b) a
  have ef11 (X0 X1 : G) : X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (hrot2 ..)
  have ef12 : x ≠ y ◇ (((y ◇ x) ◇ y) ◇ y) := mod_symm nh
  have ef25 : x ≠ x := by
    first | exact superpose ef11 ef12 | exact superpose ef12 ef11
  exact absurd rfl ef25

theorem Equation1316_termDefinableFromFin_Equation707 : Law1316.TermDefinableFromFin Law707 := by
  intro G _ M hGL
  have h : Equation707 G := Law707.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law1316.models_iff]
    exact fun x y ↦ @aux707_1316 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

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

/-- Equation 1323 `x = y ◇ (((y ◇ y) ◇ x) ◇ y)` is term-definable from equation 883
`x = y ◇ ((x ◇ y) ◇ (y ◇ y))` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux883_1323 [Finite G] [Magma G] (h : Equation883 G) (x y : G) :
    x = (y ◇ (x ◇ (y ◇ y))) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ (b ◇ b))) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 : x ≠ (y ◇ (x ◇ (y ◇ y))) ◇ y := mod_symm nh
  have ef14 : x ≠ x := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  exact absurd rfl ef14

theorem Equation1323_termDefinableFromFin_Equation883 : Law1323.TermDefinableFromFin Law883 := by
  intro G _ M hGL
  have h : Equation883 G := Law883.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law1323.models_iff]
    exact fun x y ↦ @aux883_1323 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 1526 `x = (y ◇ y) ◇ (y ◇ (x ◇ y))` is term-definable from equation 883
`x = y ◇ ((x ◇ y) ◇ (y ◇ y))` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux883_1526 [Finite G] [Magma G] (h : Equation883 G) (x y : G) :
    x = ((y ◇ x) ◇ y) ◇ (y ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ (b ◇ b))) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ b) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 : x ≠ ((y ◇ x) ◇ y) ◇ (y ◇ y) := mod_symm nh
  have ef17 : x ≠ x := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  exact absurd rfl ef17

theorem Equation1526_termDefinableFromFin_Equation883 : Law1526.TermDefinableFromFin Law883 := by
  intro G _ M hGL
  have h : Equation883 G := Law883.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law1526.models_iff]
    exact fun x y ↦ @aux883_1526 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 1086 `x = y ◇ ((x ◇ (y ◇ y)) ◇ y)` is term-definable from equation 917
`x = y ◇ ((y ◇ y) ◇ (x ◇ y))` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux917_1086 [Finite G] [Magma G] (h : Equation917 G) (x y : G) :
    x = (y ◇ ((y ◇ y) ◇ x)) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ ((b ◇ b) ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((b ◇ b) ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 : x ≠ (y ◇ ((y ◇ y) ◇ x)) ◇ y := mod_symm nh
  have ef13 : x ≠ x := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  exact absurd rfl ef13

theorem Equation1086_termDefinableFromFin_Equation917 : Law1086.TermDefinableFromFin Law917 := by
  intro G _ M hGL
  have h : Equation917 G := Law917.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law1086.models_iff]
    exact fun x y ↦ @aux917_1086 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 1729 `x = (y ◇ y) ◇ ((y ◇ x) ◇ y)` is term-definable from equation 917
`x = y ◇ ((y ◇ y) ◇ (x ◇ y))` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux917_1729 [Finite G] [Magma G] (h : Equation917 G) (x y : G) :
    x = (y ◇ y) ◇ ((y ◇ x) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ ((b ◇ b) ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((b ◇ b) ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : (b ◇ b) ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ (b ◇ b) ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : (X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 : x ≠ (y ◇ y) ◇ ((y ◇ x) ◇ y) := mod_symm nh
  have ef15 : x ≠ x := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  exact absurd rfl ef15

theorem Equation1729_termDefinableFromFin_Equation917 : Law1729.TermDefinableFromFin Law917 := by
  intro G _ M hGL
  have h : Equation917 G := Law917.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law1729.models_iff]
    exact fun x y ↦ @aux917_1729 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

/-- Equation 917 `x = y ◇ ((y ◇ y) ◇ (x ◇ y))` is term-definable from equation 1086
`x = y ◇ ((x ◇ (y ◇ y)) ◇ y)` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux1086_917 [Finite G] [Magma G] (h : Equation1086 G) (x y : G) :
    x = ((y ◇ x) ◇ (y ◇ y)) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef10 : x ≠ ((y ◇ x) ◇ (y ◇ y)) ◇ y := mod_symm nh
  have ef15 : x ≠ x := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  exact absurd rfl ef15

theorem Equation917_termDefinableFromFin_Equation1086 : Law917.TermDefinableFromFin Law1086 := by
  intro G _ M hGL
  have h : Equation1086 G := Law1086.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law917.models_iff]
    exact fun x y ↦ @aux1086_917 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 1729 `x = (y ◇ y) ◇ ((y ◇ x) ◇ y)` is term-definable from equation 1086
`x = y ◇ ((x ◇ (y ◇ y)) ◇ y)` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux1086_1729 [Finite G] [Magma G] (h : Equation1086 G) (x y : G) :
    x = (y ◇ (x ◇ y)) ◇ (y ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef10 : x ≠ (y ◇ (x ◇ y)) ◇ (y ◇ y) := mod_symm nh
  have ef13 : x ≠ x := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  exact absurd rfl ef13

theorem Equation1729_termDefinableFromFin_Equation1086 : Law1729.TermDefinableFromFin Law1086 := by
  intro G _ M hGL
  have h : Equation1086 G := Law1086.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law1729.models_iff]
    exact fun x y ↦ @aux1086_1729 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

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

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` is term-definable from equation 1276
`x = y ◇ (((x ◇ x) ◇ x) ◇ y)` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux1276_4273 [Finite G] [Magma G] (h : Equation1276 G) (x y : G) :
    x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ (a ◇ b)) ◇ (b ◇ (a ◇ b))) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ (z ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) :
      ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef10 : x ◇ (x ◇ x) ≠ y ◇ (x ◇ y) := mod_symm nh
  have ef15 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = X2 ◇ (X0 ◇ X2) := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef44 (X0 : G) : x ◇ (x ◇ x) ≠ X0 ◇ (x ◇ X0) := by
    first | exact superpose ef15 ef10 | exact superpose ef10 ef15
  subsumption ef44 ef15

theorem Equation4273_termDefinableFromFin_Equation1276 : Law4273.TermDefinableFromFin Law1276 := by
  intro G _ M hGL
  have h : Equation1276 G := Law1276.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law4273.models_iff]
    exact fun x y ↦ @aux1276_4273 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

/-- Equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` is term-definable from equation 1289
`x = y ◇ (((x ◇ y) ◇ y) ◇ y)` over finite magmas, via the term `x □ y := ((x ◇ y) ◇ x) ◇ x`. -/
private theorem aux1289_464 [Finite G] [Magma G] (h : Equation1289 G) (x y : G) :
    x = ((y ◇ (((x ◇ (((x ◇ (((x ◇ y) ◇ x) ◇ x)) ◇ x) ◇ x)) ◇ x) ◇ x)) ◇ y) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ ((a ◇ b) ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((z ◇ b) ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ (a ◇ b)) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (z ◇ b)) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef12 :
      x ≠ ((y ◇ (((x ◇ (((x ◇ (((x ◇ y) ◇ x) ◇ x)) ◇ x) ◇ x)) ◇ x) ◇ x)) ◇ y) ◇ y := mod_symm nh
  have ef17 : x ≠ ((y ◇ ((x ◇ (((x ◇ y) ◇ x) ◇ x)) ◇ x)) ◇ y) ◇ y := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef18 : x ≠ ((y ◇ (x ◇ y)) ◇ y) ◇ y := by
    first | exact superpose ef9 ef17 | exact superpose ef17 ef9
  subsumption ef18 ef10

theorem Equation464_termDefinableFromFin_Equation1289 : Law464.TermDefinableFromFin Law1289 := by
  intro G _ M hGL
  have h : Equation1289 G := Law1289.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) x) x)⟩, ?_, ?_⟩
  · rw [@Law464.models_iff]
    exact fun x y ↦ @aux1289_464 G _ M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)) (Term.var 0)), rfl⟩

/-- Equation 511 `x = y ◇ (y ◇ (y ◇ (x ◇ y)))` is term-definable from equation 1289
`x = y ◇ (((x ◇ y) ◇ y) ◇ y)` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux1289_511 [Finite G] [Magma G] (h : Equation1289 G) (x y : G) :
    x = (((y ◇ x) ◇ y) ◇ y) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ ((a ◇ b) ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((z ◇ b) ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ (a ◇ b)) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (z ◇ b)) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have hrot2 (a b : G) : (((b ◇ a) ◇ b) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ ((b ◇ z) ◇ b) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot1 z b) a
  have ef11 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1 = X0 := mod_symm (hrot2 ..)
  have ef12 : x ≠ (((y ◇ x) ◇ y) ◇ y) ◇ y := mod_symm nh
  have ef28 : x ≠ x := by
    first | exact superpose ef11 ef12 | exact superpose ef12 ef11
  exact absurd rfl ef28

theorem Equation511_termDefinableFromFin_Equation1289 : Law511.TermDefinableFromFin Law1289 := by
  intro G _ M hGL
  have h : Equation1289 G := Law1289.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law511.models_iff]
    exact fun x y ↦ @aux1289_511 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))` is term-definable from equation 1289
`x = y ◇ (((x ◇ y) ◇ y) ◇ y)` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux1289_714 [Finite G] [Magma G] (h : Equation1289 G) (x y : G) :
    x = ((y ◇ (x ◇ y)) ◇ y) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ ((a ◇ b) ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((z ◇ b) ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ (a ◇ b)) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (z ◇ b)) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef12 : x ≠ ((y ◇ (x ◇ y)) ◇ y) ◇ y := mod_symm nh
  have ef20 : x ≠ x := by
    first | exact superpose ef10 ef12 | exact superpose ef12 ef10
  exact absurd rfl ef20

theorem Equation714_termDefinableFromFin_Equation1289 : Law714.TermDefinableFromFin Law1289 := by
  intro G _ M hGL
  have h : Equation1289 G := Law1289.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law714.models_iff]
    exact fun x y ↦ @aux1289_714 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 883 `x = y ◇ ((x ◇ y) ◇ (y ◇ y))` is term-definable from equation 1323
`x = y ◇ (((y ◇ y) ◇ x) ◇ y)` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux1323_883 [Finite G] [Magma G] (h : Equation1323 G) (x y : G) :
    x = ((y ◇ y) ◇ (y ◇ x)) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ b) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ (b ◇ b) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ b) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ b) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef10 : x ≠ ((y ◇ y) ◇ (y ◇ x)) ◇ y := mod_symm nh
  have ef18 : x ≠ x := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  exact absurd rfl ef18

theorem Equation883_termDefinableFromFin_Equation1323 : Law883.TermDefinableFromFin Law1323 := by
  intro G _ M hGL
  have h : Equation1323 G := Law1323.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law883.models_iff]
    exact fun x y ↦ @aux1323_883 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 883 `x = y ◇ ((x ◇ y) ◇ (y ◇ y))` is term-definable from equation 1526
`x = (y ◇ y) ◇ (y ◇ (x ◇ y))` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux1526_883 [Finite G] [Magma G] (h : Equation1526 G) (x y : G) :
    x = ((y ◇ y) ◇ (y ◇ x)) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ b) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ b) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 : x ≠ ((y ◇ y) ◇ (y ◇ x)) ◇ y := mod_symm nh
  have ef15 : x ≠ x := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  exact absurd rfl ef15

theorem Equation883_termDefinableFromFin_Equation1526 : Law883.TermDefinableFromFin Law1526 := by
  intro G _ M hGL
  have h : Equation1526 G := Law1526.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law883.models_iff]
    exact fun x y ↦ @aux1526_883 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 1323 `x = y ◇ (((y ◇ y) ◇ x) ◇ y)` is term-definable from equation 1526
`x = (y ◇ y) ◇ (y ◇ (x ◇ y))` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux1526_1323 [Finite G] [Magma G] (h : Equation1526 G) (x y : G) :
    x = y ◇ (((y ◇ y) ◇ x) ◇ y) := by
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ b) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ b) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ (((b ◇ b) ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ ((b ◇ b) ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 : x ≠ y ◇ (((y ◇ y) ◇ x) ◇ y) := mod_symm nh
  have ef17 : x ≠ x := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  exact absurd rfl ef17

theorem Equation1323_termDefinableFromFin_Equation1526 : Law1323.TermDefinableFromFin Law1526 := by
  intro G _ M hGL
  have h : Equation1526 G := Law1526.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law1323.models_iff]
    exact fun x y ↦ @aux1526_1323 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

/-- Equation 504 `x = y ◇ (y ◇ (x ◇ (y ◇ y)))` is term-definable from equation 1722
`x = (y ◇ y) ◇ ((x ◇ y) ◇ y)` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux1722_504 [Finite G] [Magma G] (h : Equation1722 G) (x y : G) :
    x = (((y ◇ y) ◇ x) ◇ y) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ b) ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ b) ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : (((b ◇ b) ◇ a) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ ((b ◇ b) ◇ z) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef10 : x ≠ (((y ◇ y) ◇ x) ◇ y) ◇ y := mod_symm nh
  have ef16 : x ≠ x := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  exact absurd rfl ef16

theorem Equation504_termDefinableFromFin_Equation1722 : Law504.TermDefinableFromFin Law1722 := by
  intro G _ M hGL
  have h : Equation1722 G := Law1722.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law504.models_iff]
    exact fun x y ↦ @aux1722_504 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 910 `x = y ◇ ((y ◇ x) ◇ (y ◇ y))` is term-definable from equation 1722
`x = (y ◇ y) ◇ ((x ◇ y) ◇ y)` over finite magmas, via the term `x □ y := y ◇ x`. -/
private theorem aux1722_910 [Finite G] [Magma G] (h : Equation1722 G) (x y : G) :
    x = ((y ◇ y) ◇ (x ◇ y)) ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ b) ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ b) ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 : x ≠ ((y ◇ y) ◇ (x ◇ y)) ◇ y := mod_symm nh
  have ef14 : x ≠ x := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  exact absurd rfl ef14

theorem Equation910_termDefinableFromFin_Equation1722 : Law910.TermDefinableFromFin Law1722 := by
  intro G _ M hGL
  have h : Equation1722 G := Law1722.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y x)⟩, ?_, ?_⟩
  · rw [@Law910.models_iff]
    exact fun x y ↦ @aux1722_910 G _ M h x y
  · exact ⟨(tm (Term.var 1) (Term.var 0)), rfl⟩

/-- Equation 917 `x = y ◇ ((y ◇ y) ◇ (x ◇ y))` is term-definable from equation 1729
`x = (y ◇ y) ◇ ((y ◇ x) ◇ y)` over finite magmas, via the term `x □ y := x ◇ y`. -/
private theorem aux1729_917 [Finite G] [Magma G] (h : Equation1729 G) (x y : G) :
    x = y ◇ ((y ◇ y) ◇ (x ◇ y)) := by
  by_contra nh
  have hrot0 (a b : G) : b ◇ ((b ◇ b) ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ b) ◇ (z ◇ b)) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef10 : x ≠ y ◇ ((y ◇ y) ◇ (x ◇ y)) := mod_symm nh
  have ef14 : x ≠ x := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  exact absurd rfl ef14

theorem Equation917_termDefinableFromFin_Equation1729 : Law917.TermDefinableFromFin Law1729 := by
  intro G _ M hGL
  have h : Equation1729 G := Law1729.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x y)⟩, ?_, ?_⟩
  · rw [@Law917.models_iff]
    exact fun x y ↦ @aux1729_917 G _ M h x y
  · exact ⟨(tm (Term.var 0) (Term.var 1)), rfl⟩

end Law.MagmaLaw
