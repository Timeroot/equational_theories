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

/-- The defining term `x □ y := y ◇ (y ◇ x)` of equation 63 `x = y ◇ (x ◇ (x ◇ y))` can be undone:
the operation is recovered as `x ◇ y = x ◇ (y ◇ x)` read in `□` over a finite carrier. -/
private theorem inv63_d786d30cf [Finite G] [Magma G] (h : Equation63 G) (x y : G) :
    (x ◇ (x ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ x) = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef8 : x ◇ y ≠ (x ◇ (x ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ x) := mod_symm nh
  have ef15 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  exact absurd rfl ef15

/-- Equation 73 `x = y ◇ (y ◇ (x ◇ y))` holds of the term `x □ y := y ◇ (y ◇ x)` over any finite
magma satisfying equation 63 `x = y ◇ (x ◇ (x ◇ y))`. -/
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

theorem Equation73_termStructuralFromFin_Equation63 :
    Law73.TermStructuralFromFin Law63 := by
  intro G _ M hGL
  have h : Equation63 G := Law63.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law73.models_iff]
    exact fun x y ↦ @aux63_73 G _ M h x y
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv63_d786d30cf G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := x ◇ (x ◇ y)` of equation 63 `x = y ◇ (x ◇ (x ◇ y))` can be undone:
the operation is recovered as `x ◇ y = x ◇ (y ◇ x)` read in `□`. -/
private theorem inv63_f8d18577 [Magma G] (h : Equation63 G) (x y : G) :
    x ◇ (x ◇ (y ◇ (y ◇ x))) = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 : x ◇ (x ◇ (y ◇ (y ◇ x))) ≠ x ◇ y := mod_symm nh
  have ef9 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  exact absurd rfl ef9

/-- Equation 99 `x = x ◇ ((x ◇ x) ◇ x)` holds of the term `x □ y := x ◇ (x ◇ y)` over any magma
satisfying equation 63 `x = y ◇ (x ◇ (x ◇ y))`. -/
private theorem aux63_99 [Magma G] (h : Equation63 G) (x : G) :
    x = x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x))) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 : x ≠ x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x))) := mod_symm nh
  have ef9 : x ≠ x ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  subsumption ef9 ef5

theorem Equation99_termStructuralFrom_Equation63 :
    Law99.TermStructuralFrom Law63 := by
  intro G M hGL
  have h : Equation63 G := Law63.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op x y))⟩, ?_, ?_, ?_⟩
  · rw [@Law99.models_iff]
    exact fun x ↦ @aux63_99 G M h x
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv63_f8d18577 G M h (z 0) (z 1)).symm⟩

/-- Equation 118 `x = y ◇ ((x ◇ y) ◇ y)` holds of the term `x □ y := x ◇ (x ◇ y)` over any magma
satisfying equation 63 `x = y ◇ (x ◇ (x ◇ y))`. -/
private theorem aux63_118 [Magma G] (h : Equation63 G) (x y : G) :
    x = y ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ y))) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 : x ≠ y ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ y))) := mod_symm nh
  have ef9 : x ≠ y ◇ (x ◇ (x ◇ y)) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  subsumption ef9 ef5

theorem Equation118_termStructuralFrom_Equation63 :
    Law118.TermStructuralFrom Law63 := by
  intro G M hGL
  have h : Equation63 G := Law63.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op x y))⟩, ?_, ?_, ?_⟩
  · rw [@Law118.models_iff]
    exact fun x y ↦ @aux63_118 G M h x y
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv63_f8d18577 G M h (z 0) (z 1)).symm⟩

/-- Equation 125 `x = y ◇ ((y ◇ x) ◇ y)` holds of the term `x □ y := y ◇ (y ◇ x)` over any finite
magma satisfying equation 63 `x = y ◇ (x ◇ (x ◇ y))`. -/
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

theorem Equation125_termStructuralFromFin_Equation63 :
    Law125.TermStructuralFromFin Law63 := by
  intro G _ M hGL
  have h : Equation63 G := Law63.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op y (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law125.models_iff]
    exact fun x y ↦ @aux63_125 G _ M h x y
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv63_d786d30cf G _ M h (z 0) (z 1)).symm⟩

/-- Equation 4380 `x ◇ (x ◇ x) = (x ◇ x) ◇ x` holds of the term `x □ y := x ◇ (x ◇ y)` over any
magma satisfying equation 63 `x = y ◇ (x ◇ (x ◇ y))`. -/
private theorem aux63_4380 [Magma G] (h : Equation63 G) (x : G) :
    x ◇ (x ◇ (x ◇ (x ◇ x))) = (x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 : x ◇ (x ◇ (x ◇ (x ◇ x))) ≠ (x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x) := mod_symm nh
  have ef7 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0) = X1 := superpose ef5 ef5
  have ef14 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X0 = X1 := by
    first | exact superpose ef5 ef7 | exact superpose ef7 ef5
  have ef17 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = (X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef41 (X0 : G) :
      (X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0) := by
    first | exact superpose ef14 ef17 | exact superpose ef17 ef14
  have ef46 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0) := by
    first | exact superpose ef5 ef41 | exact superpose ef41 ef5
  have ef50 : x ◇ x ≠ x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef46 ef6 | exact superpose ef6 ef46
  have ef65 : x ◇ x ≠ x ◇ x := by
    first | exact superpose ef5 ef50 | exact superpose ef50 ef5
  exact absurd rfl ef65

theorem Equation4380_termStructuralFrom_Equation63 :
    Law4380.TermStructuralFrom Law63 := by
  intro G M hGL
  have h : Equation63 G := Law63.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op x y))⟩, ?_, ?_, ?_⟩
  · rw [@Law4380.models_iff]
    exact fun x ↦ @aux63_4380 G M h x
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv63_f8d18577 G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := x ◇ (x ◇ y)` of equation 63 `x = y ◇ (x ◇ (x ◇ y))` can be undone:
the operation is recovered as `x ◇ y = x ◇ (y ◇ x)` read in `□` over a finite carrier. -/
private theorem inv63_f8d18577f [Finite G] [Magma G] (h : Equation63 G) (x y : G) :
    x ◇ (x ◇ (y ◇ (y ◇ x))) = x ◇ y := by
  by_contra nh
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 : x ◇ (x ◇ (y ◇ (y ◇ x))) ≠ x ◇ y := mod_symm nh
  have ef11 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef6 ef8 | exact superpose ef8 ef6
  exact absurd rfl ef11

/-- Equation 4435 `x ◇ (y ◇ x) = (x ◇ y) ◇ x` holds of the term `x □ y := x ◇ (x ◇ y)` over any
finite magma satisfying equation 63 `x = y ◇ (x ◇ (x ◇ y))`. -/
private theorem aux63_4435 [Finite G] [Magma G] (h : Equation63 G) (x y : G) :
    x ◇ (x ◇ (y ◇ (y ◇ x))) = (x ◇ (x ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef8 : x ◇ (x ◇ (y ◇ (y ◇ x))) ≠ (x ◇ (x ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ x) := mod_symm nh
  have ef15 : x ◇ (x ◇ (y ◇ (y ◇ x))) ≠ x ◇ y := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef17 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef6 ef15 | exact superpose ef15 ef6
  exact absurd rfl ef17

theorem Equation4435_termStructuralFromFin_Equation63 :
    Law4435.TermStructuralFromFin Law63 := by
  intro G _ M hGL
  have h : Equation63 G := Law63.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op x (M.op x y))⟩, ?_, ?_, ?_⟩
  · rw [@Law4435.models_iff]
    exact fun x y ↦ @aux63_4435 G _ M h x y
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv63_f8d18577f G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := ((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ x)` of equation 65
`x = y ◇ (x ◇ (y ◇ x))` can be undone: the operation is recovered as
`x ◇ y = (y ◇ y) ◇ ((x ◇ x) ◇ x)` read in `□` over a finite carrier. -/
private theorem inv65_76b261def [Finite G] [Magma G] (h : Equation65 G) (x y : G) :
    (((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ ((((y ◇ y) ◇
      (y ◇ y)) ◇ (y ◇ y)) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ y))) = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      (((((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ ((((y ◇ y) ◇
      (y ◇ y)) ◇ (y ◇ y)) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ y))) ≠ x ◇ y := mod_symm nh
  have ef10 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = X0 ◇ ((X1 ◇ X0) ◇ X0) := superpose ef7 ef7
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef11 ef6 | exact superpose ef6 ef11
  have ef20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) = X0 ◇ ((X0 ◇ X0) ◇ X0) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef27 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) := by
    first | exact superpose ef10 ef20 | exact superpose ef20 ef10
  have ef47 (X0 : G) :
      X0 ◇ (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose ef14 ef14
  have ef57 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef11 ef47 | exact superpose ef47 ef11
  have ef82 :
      x ◇ y ≠ ((((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ y)) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ y))) := by
    first | exact superpose ef57 ef8 | exact superpose ef8 ef57
  have ef97 :
      x ◇ y ≠ ((((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇
      (((y ◇ (y ◇ y)) ◇ (y ◇ y)) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) := by
    first | exact superpose ef57 ef82 | exact superpose ef82 ef57
  have ef102 :
      x ◇ y ≠ ((((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ ((y ◇ (y ◇ y)) ◇
      (y ◇ (y ◇ y))) := by
    first | exact superpose ef27 ef97 | exact superpose ef97 ef27
  have ef105 :
      x ◇ y ≠ ((((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ y := by
    first | exact superpose ef14 ef102 | exact superpose ef102 ef14
  have ef108 :
      x ◇ y ≠ (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ y := by
    first | exact superpose ef57 ef105 | exact superpose ef105 ef57
  have ef111 :
      x ◇ y ≠ (((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇
      (((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))))) ◇ y := by
    first | exact superpose ef27 ef108 | exact superpose ef108 ef27
  have ef114 : x ◇ y ≠ (((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x))) ◇ y := by
    first | exact superpose ef14 ef111 | exact superpose ef111 ef14
  have ef117 : x ◇ y ≠ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ y := by
    first | exact superpose ef11 ef114 | exact superpose ef114 ef11
  have ef120 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef14 ef117 | exact superpose ef117 ef14
  exact absurd rfl ef120

/-- Equation 307 `x ◇ x = x ◇ (x ◇ x)` holds of the term `x □ y := ((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ x)`
over any finite magma satisfying equation 65 `x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_307 [Finite G] [Magma G] (h : Equation65 G) (x : G) :
    ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) =
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇
      x) ≠ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x) := mod_symm nh
  have ef10 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = X0 ◇ ((X1 ◇ X0) ◇ X0) := superpose ef7 ef7
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef11 ef6 | exact superpose ef6 ef11
  have ef20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) = X0 ◇ ((X0 ◇ X0) ◇ X0) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef27 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) := by
    first | exact superpose ef10 ef20 | exact superpose ef20 ef10
  have ef47 (X0 : G) :
      X0 ◇ (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose ef14 ef14
  have ef57 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef11 ef47 | exact superpose ef47 ef11
  have ef82 :
      ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) ≠ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x) := by
    first | exact superpose ef57 ef8 | exact superpose ef8 ef57
  have ef95 :
      (x ◇ (x ◇ x)) ◇ (x ◇ x) ≠ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x) := by
    first | exact superpose ef57 ef82 | exact superpose ef82 ef57
  have ef99 : x ◇ (x ◇ x) ≠ ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ x) := by
    first | exact superpose ef27 ef95 | exact superpose ef95 ef27
  have ef101 : x ◇ (x ◇ x) ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ x) := by
    first | exact superpose ef14 ef99 | exact superpose ef99 ef14
  have ef103 : (x ◇ x) ◇ (x ◇ x) ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef11 ef101 | exact superpose ef101 ef11
  subsumption ef103 ef57

theorem Equation307_termStructuralFromFin_Equation65 :
    Law307.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) (M.op y y)) (M.op x x))⟩, ?_, ?_, ?_⟩
  · rw [@Law307.models_iff]
    exact fun x ↦ @aux65_307 G _ M h x
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (tm (Term.var 1) (Term.var 1))) (tm (Term.var 0) (Term.var 0))), rfl⟩
  · exact ⟨(tm (tm (Term.var 1) (Term.var 1)) (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0))), funext fun z ↦ (@inv65_76b261def G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := ((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ y)` of equation 65
`x = y ◇ (x ◇ (y ◇ x))` can be undone: the operation is recovered as
`x ◇ y = (x ◇ (x ◇ x)) ◇ (y ◇ y)` read in `□` over a finite carrier. -/
private theorem inv65_e4ba3d91f [Finite G] [Magma G] (h : Equation65 G) (x y : G) :
    (((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ ((((y ◇ y) ◇
      (y ◇ y)) ◇ (y ◇ y)) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ y))) = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      (((((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ ((((y ◇ y) ◇
      (y ◇ y)) ◇ (y ◇ y)) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ y))) ≠ x ◇ y := mod_symm nh
  have ef10 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = X0 ◇ ((X1 ◇ X0) ◇ X0) := superpose ef7 ef7
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef11 ef6 | exact superpose ef6 ef11
  have ef20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) = X0 ◇ ((X0 ◇ X0) ◇ X0) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef27 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) := by
    first | exact superpose ef10 ef20 | exact superpose ef20 ef10
  have ef47 (X0 : G) :
      X0 ◇ (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose ef14 ef14
  have ef57 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef11 ef47 | exact superpose ef47 ef11
  have ef82 :
      x ◇ y ≠ ((((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ y)) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ y))) := by
    first | exact superpose ef57 ef8 | exact superpose ef8 ef57
  have ef97 :
      x ◇ y ≠ ((((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇
      (((y ◇ (y ◇ y)) ◇ (y ◇ y)) ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ y))) := by
    first | exact superpose ef57 ef82 | exact superpose ef82 ef57
  have ef102 :
      x ◇ y ≠ ((((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ ((y ◇ (y ◇ y)) ◇
      (y ◇ (y ◇ y))) := by
    first | exact superpose ef27 ef97 | exact superpose ef97 ef27
  have ef105 :
      x ◇ y ≠ ((((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ y := by
    first | exact superpose ef14 ef102 | exact superpose ef102 ef14
  have ef108 :
      x ◇ y ≠ (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ y := by
    first | exact superpose ef57 ef105 | exact superpose ef105 ef57
  have ef111 :
      x ◇ y ≠ (((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇
      (((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))))) ◇ y := by
    first | exact superpose ef27 ef108 | exact superpose ef108 ef27
  have ef114 : x ◇ y ≠ (((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x))) ◇ y := by
    first | exact superpose ef14 ef111 | exact superpose ef111 ef14
  have ef117 : x ◇ y ≠ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ y := by
    first | exact superpose ef11 ef114 | exact superpose ef114 ef11
  have ef120 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef14 ef117 | exact superpose ef117 ef14
  exact absurd rfl ef120

/-- Equation 614 `x = x ◇ (x ◇ ((x ◇ x) ◇ x))` holds of the term
`x □ y := ((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ y)` over any finite magma satisfying equation 65
`x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_614 [Finite G] [Magma G] (h : Equation65 G) (x : G) :
    x = ((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (((x ◇
      x) ◇ (x ◇ x)) ◇ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x))))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ≠ ((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (((x ◇
      x) ◇ (x ◇ x)) ◇ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇
      x))))) := mod_symm nh
  have ef10 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = X0 ◇ ((X1 ◇ X0) ◇ X0) := superpose ef7 ef7
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef11 ef6 | exact superpose ef6 ef11
  have ef20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) = X0 ◇ ((X0 ◇ X0) ◇ X0) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef27 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) := by
    first | exact superpose ef10 ef20 | exact superpose ef20 ef10
  have ef47 (X0 : G) :
      X0 ◇ (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose ef14 ef14
  have ef57 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef11 ef47 | exact superpose ef47 ef11
  have ef82 :
      x ≠ ((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (((x ◇
      x) ◇ (x ◇ x)) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x))))) := by
    first | exact superpose ef57 ef8 | exact superpose ef8 ef57
  have ef95 :
      x ≠ (x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇
      (((((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (x ◇ x)) ◇
      ((((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (x ◇ x)))) ◇ ((x ◇ (x ◇ x)) ◇
      (((((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (x ◇ x)) ◇
      ((((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (x ◇ x))))) := by
    first | exact superpose ef57 ef82 | exact superpose ef82 ef57
  have ef99 :
      x ≠ (x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇
      ((((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      (((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ ((x ◇ (x ◇ x)) ◇
      ((((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      (((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ x))))) := by
    first | exact superpose ef27 ef95 | exact superpose ef95 ef27
  have ef101 :
      x ≠ (x ◇ (x ◇ x)) ◇
      (((x ◇ (x ◇ x)) ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ x))))) := by
    first | exact superpose ef14 ef99 | exact superpose ef99 ef14
  have ef103 :
      x ≠ (x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))))) := by
    first | exact superpose ef11 ef101 | exact superpose ef101 ef11
  have ef105 :
      x ≠ (x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))))) := by
    first | exact superpose ef57 ef103 | exact superpose ef103 ef57
  have ef107 :
      x ≠ (x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef57 ef105 | exact superpose ef105 ef57
  have ef109 : x ≠ (x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef7 ef107 | exact superpose ef107 ef7
  have ef111 : x ≠ (x ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)) := by
    first | exact superpose ef11 ef109 | exact superpose ef109 ef11
  have ef113 : x ≠ (x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef57 ef111 | exact superpose ef111 ef57
  subsumption ef113 ef14

theorem Equation614_termStructuralFromFin_Equation65 :
    Law614.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) (M.op x x)) (M.op y y))⟩, ?_, ?_, ?_⟩
  · rw [@Law614.models_iff]
    exact fun x ↦ @aux65_614 G _ M h x
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 1) (Term.var 1))), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 1) (Term.var 1))), funext fun z ↦ (@inv65_e4ba3d91f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 817 `x = x ◇ ((x ◇ x) ◇ (x ◇ x))` holds of the term
`x □ y := ((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ y)` over any finite magma satisfying equation 65
`x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_817 [Finite G] [Magma G] (h : Equation65 G) (x : G) :
    x = ((x ◇ x) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ≠ ((x ◇ x) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) := mod_symm nh
  have ef10 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = X0 ◇ ((X1 ◇ X0) ◇ X0) := superpose ef7 ef7
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef11 ef6 | exact superpose ef6 ef11
  have ef20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) = X0 ◇ ((X0 ◇ X0) ◇ X0) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef27 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) := by
    first | exact superpose ef10 ef20 | exact superpose ef20 ef10
  have ef47 (X0 : G) :
      X0 ◇ (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose ef14 ef14
  have ef57 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef11 ef47 | exact superpose ef47 ef11
  have ef82 :
      x ≠ (x ◇ (x ◇ x)) ◇ ((((((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      ((x ◇ (x ◇ x)) ◇ (x ◇ x))))) := by
    first | exact superpose ef57 ef8 | exact superpose ef8 ef57
  have ef87 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    first | exact superpose ef57 ef6 | exact superpose ef6 ef57
  have ef90 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ X0 := by
    first | exact superpose ef7 ef87 | exact superpose ef87 ef7
  have ef95 :
      x ≠ (x ◇ (x ◇ x)) ◇ (((((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇
      ((((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef27 ef82 | exact superpose ef82 ef27
  have ef99 :
      x ≠ (x ◇ (x ◇ x)) ◇ ((((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇
      (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef90 ef95 | exact superpose ef95 ef90
  have ef101 :
      x ≠ (x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef57 ef99 | exact superpose ef99 ef57
  have ef103 :
      x ≠ (x ◇ (x ◇ x)) ◇
      (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef57 ef101 | exact superpose ef101 ef57
  have ef105 : x ≠ (x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef6 ef103 | exact superpose ef103 ef6
  subsumption ef105 ef14

theorem Equation817_termStructuralFromFin_Equation65 :
    Law817.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) (M.op x x)) (M.op y y))⟩, ?_, ?_, ?_⟩
  · rw [@Law817.models_iff]
    exact fun x ↦ @aux65_817 G _ M h x
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 1) (Term.var 1))), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 1) (Term.var 1))), funext fun z ↦ (@inv65_e4ba3d91f G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := ((x ◇ x) ◇ (x ◇ x)) ◇ y` of equation 65 `x = y ◇ (x ◇ (y ◇ x))` can
be undone: the operation is recovered as `x ◇ y = (x ◇ x) ◇ y` read in `□` over a finite
carrier. -/
private theorem inv65_979d3bc2f [Finite G] [Magma G] (h : Equation65 G) (x y : G) :
    (((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ y = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      (((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ y ≠ x ◇ y := mod_symm nh
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef11 ef6 | exact superpose ef6 ef11
  have ef47 (X0 : G) :
      X0 ◇ (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose ef14 ef14
  have ef57 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef11 ef47 | exact superpose ef47 ef11
  have ef82 :
      x ◇ y ≠ ((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ y := by
    first | exact superpose ef57 ef8 | exact superpose ef8 ef57
  have ef95 : x ◇ y ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ y := by
    first | exact superpose ef57 ef82 | exact superpose ef82 ef57
  have ef99 : x ◇ y ≠ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y := by
    first | exact superpose ef11 ef95 | exact superpose ef95 ef11
  have ef101 : x ◇ y ≠ ((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ y := by
    first | exact superpose ef57 ef99 | exact superpose ef99 ef57
  have ef103 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef7 ef101 | exact superpose ef101 ef7
  exact absurd rfl ef103

/-- Equation 872 `x = y ◇ ((x ◇ x) ◇ (y ◇ x))` holds of the term `x □ y := ((x ◇ x) ◇ (x ◇ x)) ◇ y`
over any finite magma satisfying equation 65 `x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_872 [Finite G] [Magma G] (h : Equation65 G) (x y : G) :
    x = ((y ◇ y) ◇ (y ◇ y)) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ x)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ≠ ((y ◇ y) ◇ (y ◇ y)) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇
      x)) := mod_symm nh
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef11 ef6 | exact superpose ef6 ef11
  have ef47 (X0 : G) :
      X0 ◇ (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose ef14 ef14
  have ef57 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef11 ef47 | exact superpose ef47 ef11
  have ef83 :
      x ≠ (y ◇ (y ◇ y)) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ ((y ◇ (y ◇ y)) ◇ x)) := by
    first | exact superpose ef57 ef8 | exact superpose ef8 ef57
  have ef96 :
      x ≠ (y ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇
      ((y ◇ (y ◇ y)) ◇ x)) := by
    first | exact superpose ef57 ef83 | exact superpose ef83 ef57
  have ef101 :
      x ≠ (y ◇ (y ◇ y)) ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      ((y ◇ (y ◇ y)) ◇ x)) := by
    first | exact superpose ef57 ef96 | exact superpose ef96 ef57
  have ef104 : x ≠ (y ◇ (y ◇ y)) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ ((y ◇ (y ◇ y)) ◇ x)) := by
    first | exact superpose ef11 ef101 | exact superpose ef101 ef11
  have ef107 : x ≠ (y ◇ (y ◇ y)) ◇ (((x ◇ x) ◇ (x ◇ (x ◇ x))) ◇ ((y ◇ (y ◇ y)) ◇ x)) := by
    first | exact superpose ef57 ef104 | exact superpose ef104 ef57
  have ef110 : x ≠ (y ◇ (y ◇ y)) ◇ (x ◇ ((y ◇ (y ◇ y)) ◇ x)) := by
    first | exact superpose ef7 ef107 | exact superpose ef107 ef7
  subsumption ef110 ef6

theorem Equation872_termStructuralFromFin_Equation65 :
    Law872.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) (M.op x x)) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law872.models_iff]
    exact fun x y ↦ @aux65_872 G _ M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), funext fun z ↦ (@inv65_979d3bc2f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 1426 `x = (x ◇ x) ◇ (x ◇ (x ◇ x))` holds of the term
`x □ y := ((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ y)` over any finite magma satisfying equation 65
`x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_1426 [Finite G] [Magma G] (h : Equation65 G) (x : G) :
    x = (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      x ≠ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) := mod_symm nh
  have ef10 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = X0 ◇ ((X1 ◇ X0) ◇ X0) := superpose ef7 ef7
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef11 ef6 | exact superpose ef6 ef11
  have ef20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) = X0 ◇ ((X0 ◇ X0) ◇ X0) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef27 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) := by
    first | exact superpose ef10 ef20 | exact superpose ef20 ef10
  have ef47 (X0 : G) :
      X0 ◇ (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose ef14 ef14
  have ef57 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef11 ef47 | exact superpose ef47 ef11
  have ef82 :
      x ≠ ((((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))))) := by
    first | exact superpose ef57 ef8 | exact superpose ef8 ef57
  have ef95 :
      x ≠ (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇
      (((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef27 ef82 | exact superpose ef82 ef27
  have ef99 :
      x ≠ (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef14 ef95 | exact superpose ef95 ef14
  have ef101 : x ≠ ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef57 ef99 | exact superpose ef99 ef57
  have ef103 : x ≠ (x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef11 ef101 | exact superpose ef101 ef11
  subsumption ef103 ef14

theorem Equation1426_termStructuralFromFin_Equation65 :
    Law1426.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) (M.op x x)) (M.op y y))⟩, ?_, ?_, ?_⟩
  · rw [@Law1426.models_iff]
    exact fun x ↦ @aux65_1426 G _ M h x
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 1) (Term.var 1))), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 1) (Term.var 1))), funext fun z ↦ (@inv65_e4ba3d91f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3253 `x ◇ x = x ◇ (x ◇ (x ◇ x))` holds of the term
`x □ y := ((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ x)` over any finite magma satisfying equation 65
`x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_3253 [Finite G] [Magma G] (h : Equation65 G) (x : G) :
    ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) =
      ((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x))) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (x ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇
      x) ≠ ((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x))) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (x ◇
      x) := mod_symm nh
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef11 ef6 | exact superpose ef6 ef11
  have ef47 (X0 : G) :
      X0 ◇ (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose ef14 ef14
  have ef57 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef11 ef47 | exact superpose ef47 ef11
  have ef83 :
      ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) ≠ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (x ◇
      x) := by
    first | exact superpose ef57 ef8 | exact superpose ef8 ef57
  have ef88 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    first | exact superpose ef57 ef6 | exact superpose ef6 ef57
  have ef91 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ X0 := by
    first | exact superpose ef7 ef88 | exact superpose ef88 ef7
  have ef96 :
      ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) ≠ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (x ◇
      x) := by
    first | exact superpose ef57 ef83 | exact superpose ef83 ef57
  have ef101 :
      (x ◇ x) ◇ (x ◇ x) ≠ (((((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (x ◇
      x) := by
    first | exact superpose ef91 ef96 | exact superpose ef96 ef91
  have ef104 :
      (x ◇ x) ◇ (x ◇ x) ≠ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (x ◇ x) := by
    first | exact superpose ef57 ef101 | exact superpose ef101 ef57
  have ef107 :
      (x ◇ x) ◇ (x ◇ x) ≠ (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      (x ◇ x) := by
    first | exact superpose ef7 ef104 | exact superpose ef104 ef7
  have ef110 :
      (x ◇ x) ◇ (x ◇ x) ≠ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x) := by
    first | exact superpose ef57 ef107 | exact superpose ef107 ef57
  have ef113 : (x ◇ x) ◇ (x ◇ x) ≠ (x ◇ x) ◇ (x ◇ x) := by
    first | exact superpose ef7 ef110 | exact superpose ef110 ef7
  exact absurd rfl ef113

theorem Equation3253_termStructuralFromFin_Equation65 :
    Law3253.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) (M.op y y)) (M.op x x))⟩, ?_, ?_, ?_⟩
  · rw [@Law3253.models_iff]
    exact fun x ↦ @aux65_3253 G _ M h x
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (tm (Term.var 1) (Term.var 1))) (tm (Term.var 0) (Term.var 0))), rfl⟩
  · exact ⟨(tm (tm (Term.var 1) (Term.var 1)) (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0))), funext fun z ↦ (@inv65_76b261def G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3456 `x ◇ x = x ◇ ((x ◇ x) ◇ x)` holds of the term
`x □ y := ((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ x)` over any finite magma satisfying equation 65
`x = y ◇ (x ◇ (y ◇ x))`. -/
private theorem aux65_3456 [Finite G] [Magma G] (h : Equation65 G) (x : G) :
    ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) = (((((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ (x ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef6 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef8 :
      ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) ≠ (((((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ (x ◇
      x) := mod_symm nh
  have ef10 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = X0 ◇ ((X1 ◇ X0) ◇ X0) := superpose ef7 ef7
  have ef11 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef6 ef7 | exact superpose ef7 ef6
  have ef14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef11 ef6 | exact superpose ef6 ef11
  have ef20 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) = X0 ◇ ((X0 ◇ X0) ◇ X0) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef27 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0) := by
    first | exact superpose ef10 ef20 | exact superpose ef20 ef10
  have ef47 (X0 : G) :
      X0 ◇ (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose ef14 ef14
  have ef57 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef11 ef47 | exact superpose ef47 ef11
  have ef82 :
      ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) ≠ ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ (x ◇ x) := by
    first | exact superpose ef57 ef8 | exact superpose ef8 ef57
  have ef95 :
      (x ◇ (x ◇ x)) ◇ (x ◇ x) ≠ (((x ◇ (x ◇ x)) ◇
      (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ (x ◇ x) := by
    first | exact superpose ef57 ef82 | exact superpose ef82 ef57
  have ef99 :
      x ◇ (x ◇ x) ≠ (((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇
      (((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))))) ◇ (x ◇ x) := by
    first | exact superpose ef27 ef95 | exact superpose ef95 ef27
  have ef101 :
      x ◇ (x ◇ x) ≠ (((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ x))) ◇
      (x ◇ x) := by
    first | exact superpose ef14 ef99 | exact superpose ef99 ef14
  have ef103 : x ◇ (x ◇ x) ≠ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (x ◇ x) := by
    first | exact superpose ef11 ef101 | exact superpose ef101 ef11
  have ef105 : x ◇ (x ◇ x) ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef14 ef103 | exact superpose ef103 ef14
  exact absurd rfl ef105

theorem Equation3456_termStructuralFromFin_Equation65 :
    Law3456.TermStructuralFromFin Law65 := by
  intro G _ M hGL
  have h : Equation65 G := Law65.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) (M.op y y)) (M.op x x))⟩, ?_, ?_, ?_⟩
  · rw [@Law3456.models_iff]
    exact fun x ↦ @aux65_3456 G _ M h x
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (tm (Term.var 1) (Term.var 1))) (tm (Term.var 0) (Term.var 0))), rfl⟩
  · exact ⟨(tm (tm (Term.var 1) (Term.var 1)) (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0))), funext fun z ↦ (@inv65_76b261def G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := (x ◇ x) ◇ y` of equation 66 `x = y ◇ (x ◇ (y ◇ y))` can be undone:
the operation is recovered as `x ◇ y = (x ◇ (x ◇ x)) ◇ y` read in `□`. -/
private theorem inv66_b17ab2c2 [Magma G] (h : Equation66 G) (x y : G) :
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

/-- Equation 53 `x = x ◇ (y ◇ (x ◇ y))` holds of the term `x □ y := (x ◇ x) ◇ y` over any magma
satisfying equation 66 `x = y ◇ (x ◇ (y ◇ y))`. -/
private theorem aux66_53 [Magma G] (h : Equation66 G) (x y : G) :
    x = (x ◇ x) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ y)) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 : x ≠ (x ◇ x) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ y)) := mod_symm nh
  have ef7 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 := superpose ef5 ef5
  have ef8 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef13 : x ≠ (x ◇ x) ◇ (x ◇ x) := by
    first | exact superpose ef8 ef6 | exact superpose ef6 ef8
  subsumption ef13 ef7

theorem Equation53_termStructuralFrom_Equation66 :
    Law53.TermStructuralFrom Law66 := by
  intro G M hGL
  have h : Equation66 G := Law66.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law53.models_iff]
    exact fun x y ↦ @aux66_53 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv66_b17ab2c2 G M h (z 0) (z 1)).symm⟩

/-- Equation 1020 `x = x ◇ ((x ◇ (x ◇ x)) ◇ x)` holds of the term `x □ y := (x ◇ x) ◇ y` over any
magma satisfying equation 66 `x = y ◇ (x ◇ (y ◇ y))`. -/
private theorem aux66_1020 [Magma G] (h : Equation66 G) (x : G) :
    x = (x ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ x) ◇ ((((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) := mod_symm nh
  have ef7 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 := superpose ef5 ef5
  have ef8 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef14 : x ≠ ((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef8 ef6 | exact superpose ef6 ef8
  have ef16 : x ≠ (x ◇ x) ◇ (x ◇ x) := by
    first | exact superpose ef8 ef14 | exact superpose ef14 ef8
  subsumption ef16 ef7

theorem Equation1020_termStructuralFrom_Equation66 :
    Law1020.TermStructuralFrom Law66 := by
  intro G M hGL
  have h : Equation66 G := Law66.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1020.models_iff]
    exact fun x ↦ @aux66_1020 G M h x
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv66_b17ab2c2 G M h (z 0) (z 1)).symm⟩

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

/-- Equation 1036 `x = x ◇ ((y ◇ (x ◇ x)) ◇ y)` holds of the term `x □ y := (y ◇ y) ◇ x` over any
magma satisfying equation 66 `x = y ◇ (x ◇ (y ◇ y))`. -/
private theorem aux66_1036 [Magma G] (h : Equation66 G) (x y : G) :
    x = (((y ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇
      ((y ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y))) ◇ x := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((y ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y)) ◇
      ((y ◇ y) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ y))) ◇ x := mod_symm nh
  have ef7 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 := superpose ef5 ef5
  have ef8 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef12 (X0 X1 : G) : X1 ◇ X1 = ((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0 := superpose ef8 ef8
  have ef13 : x ≠ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x := by
    first | exact superpose ef8 ef6 | exact superpose ef6 ef8
  have ef15 : x ≠ ((x ◇ x) ◇ x) ◇ x := by
    first | exact superpose ef7 ef13 | exact superpose ef13 ef7
  have ef20 (X0 X1 : G) :
      X1 ◇ X1 = ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose ef12 ef12
  have ef23 (X0 X1 : G) : X1 ◇ X1 = X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef20 | exact superpose ef20 ef7
  have ef29 (X0 X1 : G) : (X0 ◇ X1) ◇ (X0 ◇ X0) = X1 := by
    first | exact superpose ef23 ef5 | exact superpose ef5 ef23
  have ef90 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) ◇ X0 = X1 := superpose ef29 ef29
  have ef157 : x ≠ x := by
    first | exact superpose ef90 ef15 | exact superpose ef15 ef90
  exact absurd rfl ef157

theorem Equation1036_termStructuralFrom_Equation66 :
    Law1036.TermStructuralFrom Law66 := by
  intro G M hGL
  have h : Equation66 G := Law66.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law1036.models_iff]
    exact fun x y ↦ @aux66_1036 G M h x y
  · exact ⟨(tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0))), funext fun z ↦ (@inv66_dfe2c1ca G M h (z 0) (z 1)).symm⟩

/-- Equation 1038 `x = x ◇ ((y ◇ (x ◇ y)) ◇ x)` holds of the term `x □ y := (x ◇ x) ◇ y` over any
magma satisfying equation 66 `x = y ◇ (x ◇ (y ◇ y))`. -/
private theorem aux66_1038 [Magma G] (h : Equation66 G) (x y : G) :
    x = (x ◇ x) ◇ ((((y ◇ y) ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ y))) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ x) ◇ ((((y ◇ y) ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ y))) ◇ x) := mod_symm nh
  have ef7 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 := superpose ef5 ef5
  have ef8 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef14 : x ≠ ((y ◇ y) ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ y)) := by
    first | exact superpose ef8 ef6 | exact superpose ef6 ef8
  have ef16 : x ≠ (x ◇ x) ◇ (x ◇ x) := by
    first | exact superpose ef8 ef14 | exact superpose ef14 ef8
  subsumption ef16 ef7

theorem Equation1038_termStructuralFrom_Equation66 :
    Law1038.TermStructuralFrom Law66 := by
  intro G M hGL
  have h : Equation66 G := Law66.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1038.models_iff]
    exact fun x y ↦ @aux66_1038 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv66_b17ab2c2 G M h (z 0) (z 1)).symm⟩

/-- Equation 1073 `x = y ◇ ((x ◇ (x ◇ x)) ◇ y)` holds of the term `x □ y := (x ◇ x) ◇ y` over any
magma satisfying equation 66 `x = y ◇ (x ◇ (y ◇ y))`. -/
private theorem aux66_1073 [Magma G] (h : Equation66 G) (x y : G) :
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

theorem Equation1073_termStructuralFrom_Equation66 :
    Law1073.TermStructuralFrom Law66 := by
  intro G M hGL
  have h : Equation66 G := Law66.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1073.models_iff]
    exact fun x y ↦ @aux66_1073 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv66_b17ab2c2 G M h (z 0) (z 1)).symm⟩

/-- Equation 1075 `x = y ◇ ((x ◇ (x ◇ y)) ◇ x)` holds of the term `x □ y := (y ◇ y) ◇ x` over any
magma satisfying equation 66 `x = y ◇ (x ◇ (y ◇ y))`. -/
private theorem aux66_1075 [Magma G] (h : Equation66 G) (x y : G) :
    x = (((x ◇ x) ◇ ((((y ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ x)) ◇
      ((x ◇ x) ◇ ((((y ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ x))) ◇ y := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((x ◇ x) ◇ ((((y ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ x)) ◇
      ((x ◇ x) ◇ ((((y ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ x))) ◇ y := mod_symm nh
  have ef7 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 := superpose ef5 ef5
  have ef8 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef12 (X0 X1 : G) : X1 ◇ X1 = ((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0 := superpose ef8 ef8
  have ef13 : x ≠ ((((y ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x))) ◇ y := by
    first | exact superpose ef8 ef6 | exact superpose ef6 ef8
  have ef15 : x ≠ ((y ◇ y) ◇ x) ◇ y := by
    first | exact superpose ef7 ef13 | exact superpose ef13 ef7
  have ef20 (X0 X1 : G) :
      X1 ◇ X1 = ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose ef12 ef12
  have ef23 (X0 X1 : G) : X1 ◇ X1 = X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef20 | exact superpose ef20 ef7
  have ef29 (X0 X1 : G) : (X0 ◇ X1) ◇ (X0 ◇ X0) = X1 := by
    first | exact superpose ef23 ef5 | exact superpose ef5 ef23
  have ef90 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) ◇ X0 = X1 := superpose ef29 ef29
  have ef157 : x ≠ x := by
    first | exact superpose ef90 ef15 | exact superpose ef15 ef90
  exact absurd rfl ef157

theorem Equation1075_termStructuralFrom_Equation66 :
    Law1075.TermStructuralFrom Law66 := by
  intro G M hGL
  have h : Equation66 G := Law66.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law1075.models_iff]
    exact fun x y ↦ @aux66_1075 G M h x y
  · exact ⟨(tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0))), funext fun z ↦ (@inv66_dfe2c1ca G M h (z 0) (z 1)).symm⟩

/-- Equation 1113 `x = y ◇ ((y ◇ (x ◇ y)) ◇ y)` holds of the term `x □ y := (x ◇ x) ◇ y` over any
magma satisfying equation 66 `x = y ◇ (x ◇ (y ◇ y))`. -/
private theorem aux66_1113 [Magma G] (h : Equation66 G) (x y : G) :
    x = (y ◇ y) ◇ ((((y ◇ y) ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ y))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (y ◇ y) ◇ ((((y ◇ y) ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ y))) ◇ y) := mod_symm nh
  have ef7 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 := superpose ef5 ef5
  have ef8 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef14 : x ≠ ((y ◇ y) ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ y) ◇ ((x ◇ x) ◇ y)) := by
    first | exact superpose ef8 ef6 | exact superpose ef6 ef8
  have ef16 : x ≠ (x ◇ x) ◇ (x ◇ x) := by
    first | exact superpose ef8 ef14 | exact superpose ef14 ef8
  subsumption ef16 ef7

theorem Equation1113_termStructuralFrom_Equation66 :
    Law1113.TermStructuralFrom Law66 := by
  intro G M hGL
  have h : Equation66 G := Law66.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1113.models_iff]
    exact fun x y ↦ @aux66_1113 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv66_b17ab2c2 G M h (z 0) (z 1)).symm⟩

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` holds of the term `x □ y := (x ◇ x) ◇ y` over any
magma satisfying equation 66 `x = y ◇ (x ◇ (y ◇ y))`. -/
private theorem aux66_4273 [Magma G] (h : Equation66 G) (x y : G) :
    (x ◇ x) ◇ ((x ◇ x) ◇ x) = (y ◇ y) ◇ ((x ◇ x) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 : (x ◇ x) ◇ ((x ◇ x) ◇ x) ≠ (y ◇ y) ◇ ((x ◇ x) ◇ y) := mod_symm nh
  have ef7 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ X0) = X0 := superpose ef5 ef5
  have ef8 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X0) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef13 : x ◇ x ≠ (x ◇ x) ◇ ((x ◇ x) ◇ x) := by
    first | exact superpose ef8 ef6 | exact superpose ef6 ef8
  subsumption ef13 ef8

theorem Equation4273_termStructuralFrom_Equation66 :
    Law4273.TermStructuralFrom Law66 := by
  intro G M hGL
  have h : Equation66 G := Law66.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law4273.models_iff]
    exact fun x y ↦ @aux66_4273 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv66_b17ab2c2 G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := (y ◇ x) ◇ y` of equation 73 `x = y ◇ (y ◇ (x ◇ y))` can be undone:
the operation is recovered as `x ◇ y = (x ◇ y) ◇ y` read in `□` over a finite carrier. -/
private theorem inv73_fa411fc9f [Finite G] [Magma G] (h : Equation73 G) (x y : G) :
    (y ◇ ((y ◇ x) ◇ y)) ◇ y = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 : (y ◇ ((y ◇ x) ◇ y)) ◇ y ≠ x ◇ y := mod_symm nh
  have ef16 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  exact absurd rfl ef16

/-- Equation 8 `x = x ◇ (x ◇ x)` holds of the term `x □ y := (y ◇ x) ◇ y` over any finite magma
satisfying equation 73 `x = y ◇ (y ◇ (x ◇ y))`. -/
private theorem aux73_8 [Finite G] [Magma G] (h : Equation73 G) (x : G) :
    x = (((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 : x ≠ (((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x) := mod_symm nh
  have ef12 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef13 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)) = X1 := superpose ef8 ef8
  have ef29 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  subsumption ef29 ef13

theorem Equation8_termStructuralFromFin_Equation73 :
    Law8.TermStructuralFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law8.models_iff]
    exact fun x ↦ @aux73_8 G _ M h x
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv73_fa411fc9f G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := (x ◇ y) ◇ x` of equation 73 `x = y ◇ (y ◇ (x ◇ y))` can be undone:
the operation is recovered as `x ◇ y = y ◇ (y ◇ x)` read in `□` over a finite carrier. -/
private theorem inv73_e9e004b8f [Finite G] [Magma G] (h : Equation73 G) (x y : G) :
    (y ◇ ((y ◇ x) ◇ y)) ◇ y = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 : (y ◇ ((y ◇ x) ◇ y)) ◇ y ≠ x ◇ y := mod_symm nh
  have ef16 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  exact absurd rfl ef16

/-- Equation 63 `x = y ◇ (x ◇ (x ◇ y))` holds of the term `x □ y := (x ◇ y) ◇ x` over any finite
magma satisfying equation 73 `x = y ◇ (y ◇ (x ◇ y))`. -/
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

theorem Equation63_termStructuralFromFin_Equation73 :
    Law63.TermStructuralFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law63.models_iff]
    exact fun x y ↦ @aux73_63 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv73_e9e004b8f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 411 `x = x ◇ (x ◇ (x ◇ (x ◇ x)))` holds of the term `x □ y := (y ◇ x) ◇ y` over any
finite magma satisfying equation 73 `x = y ◇ (y ◇ (x ◇ y))`. -/
private theorem aux73_411 [Finite G] [Magma G] (h : Equation73 G) (x : G) :
    x =
      (((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      x ≠ (((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇
      x) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) := mod_symm nh
  have ef12 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef31 :
      x ≠ ((((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇
      x) ◇ (((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x) ◇
      (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef32 :
      x ≠ (((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇
      (x ◇
      (((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef12 ef31 | exact superpose ef31 ef12
  have ef38 :
      x ≠ ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))))) ◇
      (x ◇
      ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))))) := by
    first | exact superpose ef12 ef32 | exact superpose ef32 ef12
  have ef42 :
      x ≠ (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (x ◇
      (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x))))))) := by
    first | exact superpose ef12 ef38 | exact superpose ef38 ef12
  have ef46 : x ≠ (x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef15 ef42 | exact superpose ef42 ef15
  subsumption ef46 ef15

theorem Equation411_termStructuralFromFin_Equation73 :
    Law411.TermStructuralFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law411.models_iff]
    exact fun x ↦ @aux73_411 G _ M h x
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv73_fa411fc9f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 1020 `x = x ◇ ((x ◇ (x ◇ x)) ◇ x)` holds of the term `x □ y := (y ◇ x) ◇ y` over any
finite magma satisfying equation 73 `x = y ◇ (y ◇ (x ◇ y))`. -/
private theorem aux73_1020 [Finite G] [Magma G] (h : Equation73 G) (x : G) :
    x = (((x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      ((x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      x ≠ (((x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      ((x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) := mod_symm nh
  have ef12 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef30 :
      x ≠ (((x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ x) ◇ x) ◇
      ((x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ x) := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef33 :
      x ≠ ((x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ x) ◇
      (x ◇ ((x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ x)) := by
    first | exact superpose ef12 ef30 | exact superpose ef30 ef12
  have ef39 :
      x ≠ ((x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ x) ◇
      (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef9 ef33 | exact superpose ef33 ef9
  have ef43 :
      x ≠ ((x ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x))))) ◇ x) ◇
      ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef12 ef39 | exact superpose ef39 ef12
  have ef47 : x ≠ ((x ◇ x) ◇ x) ◇ x := by
    first | exact superpose ef15 ef43 | exact superpose ef43 ef15
  have ef51 : x ≠ (x ◇ (x ◇ x)) ◇ x := by
    first | exact superpose ef12 ef47 | exact superpose ef47 ef12
  subsumption ef51 ef8

theorem Equation1020_termStructuralFromFin_Equation73 :
    Law1020.TermStructuralFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1020.models_iff]
    exact fun x ↦ @aux73_1020 G _ M h x
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv73_fa411fc9f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 1629 `x = (x ◇ x) ◇ ((x ◇ x) ◇ x)` holds of the term `x □ y := (x ◇ y) ◇ x` over any
finite magma satisfying equation 73 `x = y ◇ (y ◇ (x ◇ y))`. -/
private theorem aux73_1629 [Finite G] [Magma G] (h : Equation73 G) (x : G) :
    x = (((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      x ≠ (((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ x) := mod_symm nh
  have ef16 : x ≠ x ◇ ((x ◇ x) ◇ x) := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  subsumption ef16 ef9

theorem Equation1629_termStructuralFromFin_Equation73 :
    Law1629.TermStructuralFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law1629.models_iff]
    exact fun x ↦ @aux73_1629 G _ M h x
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv73_e9e004b8f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 1685 `x = (y ◇ x) ◇ ((x ◇ y) ◇ y)` holds of the term `x □ y := (y ◇ x) ◇ y` over any
finite magma satisfying equation 73 `x = y ◇ (y ◇ (x ◇ y))`. -/
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

theorem Equation1685_termStructuralFromFin_Equation73 :
    Law1685.TermStructuralFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1685.models_iff]
    exact fun x y ↦ @aux73_1685 G _ M h x y
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv73_fa411fc9f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 1692 `x = (y ◇ x) ◇ ((y ◇ x) ◇ y)` holds of the term `x □ y := (x ◇ y) ◇ x` over any
finite magma satisfying equation 73 `x = y ◇ (y ◇ (x ◇ y))`. -/
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

theorem Equation1692_termStructuralFromFin_Equation73 :
    Law1692.TermStructuralFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law1692.models_iff]
    exact fun x y ↦ @aux73_1692 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv73_e9e004b8f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3253 `x ◇ x = x ◇ (x ◇ (x ◇ x))` holds of the term `x □ y := (y ◇ x) ◇ y` over any
finite magma satisfying equation 73 `x = y ◇ (y ◇ (x ◇ y))`. -/
private theorem aux73_3253 [Finite G] [Magma G] (h : Equation73 G) (x : G) :
    (x ◇ x) ◇ x = (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      (x ◇ x) ◇ x ≠ (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) := mod_symm nh
  have ef12 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef30 :
      x ◇ (x ◇ x) ≠ ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x) ◇
      (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef31 :
      x ◇ (x ◇ x) ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇
      (x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef12 ef30 | exact superpose ef30 ef12
  have ef36 :
      x ◇ (x ◇ x) ≠ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef12 ef31 | exact superpose ef31 ef12
  have ef39 : x ◇ (x ◇ x) ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef15 ef36 | exact superpose ef36 ef15
  exact absurd rfl ef39

theorem Equation3253_termStructuralFromFin_Equation73 :
    Law3253.TermStructuralFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3253.models_iff]
    exact fun x ↦ @aux73_3253 G _ M h x
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv73_fa411fc9f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3319 `x ◇ y = x ◇ (y ◇ (y ◇ y))` holds of the term `x □ y := (y ◇ x) ◇ y` over any
finite magma satisfying equation 73 `x = y ◇ (y ◇ (x ◇ y))`. -/
private theorem aux73_3319 [Finite G] [Magma G] (h : Equation73 G) (x y : G) :
    (y ◇ x) ◇ y = (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ x) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      (y ◇ x) ◇ y ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ x) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) := mod_symm nh
  have ef12 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef25 :
      (y ◇ x) ◇ y ≠ ((((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) ◇ x) ◇
      (((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef32 :
      (y ◇ x) ◇ y ≠ (((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) ◇
      (x ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y)))) := by
    first | exact superpose ef12 ef25 | exact superpose ef25 ef12
  have ef36 :
      (y ◇ x) ◇ y ≠ ((y ◇ (y ◇ y)) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ (y ◇ (y ◇ y))))) := by
    first | exact superpose ef12 ef32 | exact superpose ef32 ef12
  have ef39 : (y ◇ x) ◇ y ≠ y ◇ (x ◇ y) := by
    first | exact superpose ef15 ef36 | exact superpose ef36 ef15
  subsumption ef39 ef12

theorem Equation3319_termStructuralFromFin_Equation73 :
    Law3319.TermStructuralFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3319.models_iff]
    exact fun x y ↦ @aux73_3319 G _ M h x y
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv73_fa411fc9f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3456 `x ◇ x = x ◇ ((x ◇ x) ◇ x)` holds of the term `x □ y := (x ◇ y) ◇ x` over any
finite magma satisfying equation 73 `x = y ◇ (y ◇ (x ◇ y))`. -/
private theorem aux73_3456 [Finite G] [Magma G] (h : Equation73 G) (x : G) :
    (x ◇ x) ◇ x = (x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 : (x ◇ x) ◇ x ≠ (x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x := mod_symm nh
  have ef12 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef29 : x ◇ (x ◇ x) ≠ (x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ x := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef32 : x ◇ (x ◇ x) ≠ x ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x) := by
    first | exact superpose ef12 ef29 | exact superpose ef29 ef12
  have ef37 : x ◇ (x ◇ x) ≠ x ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ x) := by
    first | exact superpose ef12 ef32 | exact superpose ef32 ef12
  have ef40 : x ◇ (x ◇ x) ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef15 ef37 | exact superpose ef37 ef15
  exact absurd rfl ef40

theorem Equation3456_termStructuralFromFin_Equation73 :
    Law3456.TermStructuralFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law3456.models_iff]
    exact fun x ↦ @aux73_3456 G _ M h x
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv73_e9e004b8f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3522 `x ◇ y = x ◇ ((y ◇ y) ◇ y)` holds of the term `x □ y := (x ◇ y) ◇ x` over any
finite magma satisfying equation 73 `x = y ◇ (y ◇ (x ◇ y))`. -/
private theorem aux73_3522 [Finite G] [Magma G] (h : Equation73 G) (x y : G) :
    (x ◇ y) ◇ x = (x ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ x := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ a) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef10 : (x ◇ y) ◇ x ≠ (x ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ x := mod_symm nh
  have ef12 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef15 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef30 : (x ◇ y) ◇ x ≠ (x ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y)))) ◇ x := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef31 : (x ◇ y) ◇ x ≠ x ◇ ((((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) ◇ x) := by
    first | exact superpose ef12 ef30 | exact superpose ef30 ef12
  have ef36 : (x ◇ y) ◇ x ≠ x ◇ (((y ◇ (y ◇ y)) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ x) := by
    first | exact superpose ef12 ef31 | exact superpose ef31 ef12
  have ef39 : (x ◇ y) ◇ x ≠ x ◇ (y ◇ x) := by
    first | exact superpose ef15 ef36 | exact superpose ef36 ef15
  subsumption ef39 ef12

theorem Equation3522_termStructuralFromFin_Equation73 :
    Law3522.TermStructuralFromFin Law73 := by
  intro G _ M hGL
  have h : Equation73 G := Law73.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law3522.models_iff]
    exact fun x y ↦ @aux73_3522 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv73_e9e004b8f G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := (y ◇ x) ◇ y` of equation 118 `x = y ◇ ((x ◇ y) ◇ y)` can be undone:
the operation is recovered as `x ◇ y = (y ◇ x) ◇ x` read in `□` over a finite carrier. -/
private theorem inv118_fa411fc9f [Finite G] [Magma G] (h : Equation118 G) (x y : G) :
    (x ◇ ((x ◇ y) ◇ x)) ◇ x = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 : x ◇ y ≠ (x ◇ ((x ◇ y) ◇ x)) ◇ x := mod_symm nh
  have ef14 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  exact absurd rfl ef14

/-- Equation 8 `x = x ◇ (x ◇ x)` holds of the term `x □ y := (y ◇ x) ◇ y` over any finite magma
satisfying equation 118 `x = y ◇ ((x ◇ y) ◇ y)`. -/
private theorem aux118_8 [Finite G] [Magma G] (h : Equation118 G) (x : G) :
    x = (((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef9 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef10 : x ≠ (((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x) := mod_symm nh
  have ef18 : x ≠ x ◇ ((x ◇ x) ◇ x) := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  subsumption ef18 ef7

theorem Equation8_termStructuralFromFin_Equation118 :
    Law8.TermStructuralFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law8.models_iff]
    exact fun x ↦ @aux118_8 G _ M h x
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 0)), funext fun z ↦ (@inv118_fa411fc9f G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := (x ◇ y) ◇ x` of equation 118 `x = y ◇ ((x ◇ y) ◇ y)` can be undone:
the operation is recovered as `x ◇ y = x ◇ (x ◇ y)` read in `□` over a finite carrier. -/
private theorem inv118_e9e004b8f [Finite G] [Magma G] (h : Equation118 G) (x y : G) :
    (x ◇ ((x ◇ y) ◇ x)) ◇ x = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 : x ◇ y ≠ (x ◇ ((x ◇ y) ◇ x)) ◇ x := mod_symm nh
  have ef14 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  exact absurd rfl ef14

/-- Equation 63 `x = y ◇ (x ◇ (x ◇ y))` holds of the term `x □ y := (x ◇ y) ◇ x` over any finite
magma satisfying equation 118 `x = y ◇ ((x ◇ y) ◇ y)`. -/
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

theorem Equation63_termStructuralFromFin_Equation118 :
    Law63.TermStructuralFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law63.models_iff]
    exact fun x y ↦ @aux118_63 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (Term.var 1))), funext fun z ↦ (@inv118_e9e004b8f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 411 `x = x ◇ (x ◇ (x ◇ (x ◇ x)))` holds of the term `x □ y := (y ◇ x) ◇ y` over any
finite magma satisfying equation 118 `x = y ◇ ((x ◇ y) ◇ y)`. -/
private theorem aux118_411 [Finite G] [Magma G] (h : Equation118 G) (x : G) :
    x =
      (((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef10 :
      x ≠ (((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇
      x) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) := mod_symm nh
  have ef13 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := superpose ef8 ef8
  have ef18 :
      x ≠ ((((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef19 :
      x ≠ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇
      (x ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))) := by
    first | exact superpose ef13 ef18 | exact superpose ef18 ef13
  have ef21 :
      x ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))))) := by
    first | exact superpose ef13 ef19 | exact superpose ef19 ef13
  have ef22 : x ≠ (x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef7 ef21 | exact superpose ef21 ef7
  have ef30 (X0 : G) : X0 ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef13 ef7 | exact superpose ef7 ef13
  have ef54 : x ≠ (x ◇ (x ◇ x)) ◇ x := by
    first | exact superpose ef30 ef22 | exact superpose ef22 ef30
  subsumption ef54 ef8

theorem Equation411_termStructuralFromFin_Equation118 :
    Law411.TermStructuralFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law411.models_iff]
    exact fun x ↦ @aux118_411 G _ M h x
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 0)), funext fun z ↦ (@inv118_fa411fc9f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 1020 `x = x ◇ ((x ◇ (x ◇ x)) ◇ x)` holds of the term `x □ y := (y ◇ x) ◇ y` over any
finite magma satisfying equation 118 `x = y ◇ ((x ◇ y) ◇ y)`. -/
private theorem aux118_1020 [Finite G] [Magma G] (h : Equation118 G) (x : G) :
    x = (((x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      ((x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) := by
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
      x ≠ (((x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      ((x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) := mod_symm nh
  have ef13 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := superpose ef8 ef8
  have ef15 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1)) = X1 := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef28 (X0 X1 : G) : X0 ◇ (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  have ef40 :
      x ≠ (((x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ x) ◇ x) ◇
      ((x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ x) := by
    first | exact superpose ef13 ef10 | exact superpose ef10 ef13
  have ef43 :
      x ≠ ((x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ x) ◇
      (x ◇ ((x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇ x)) := by
    first | exact superpose ef13 ef40 | exact superpose ef40 ef13
  have ef49 :
      x ≠ (x ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x)) ◇
      (x ◇ (x ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x))) := by
    first | exact superpose ef13 ef43 | exact superpose ef43 ef13
  have ef53 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇
      (x ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x)) := by
    first | exact superpose ef28 ef49 | exact superpose ef49 ef28
  have ef57 :
      x ≠ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇
      (x ◇ (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ x)) := by
    first | exact superpose ef13 ef53 | exact superpose ef53 ef13
  have ef60 : x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ x)) := by
    first | exact superpose ef28 ef57 | exact superpose ef57 ef28
  have ef61 : x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) := by
    first | exact superpose ef13 ef60 | exact superpose ef60 ef13
  have ef62 : x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef8 ef61 | exact superpose ef61 ef8
  subsumption ef62 ef15

theorem Equation1020_termStructuralFromFin_Equation118 :
    Law1020.TermStructuralFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1020.models_iff]
    exact fun x ↦ @aux118_1020 G _ M h x
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 0)), funext fun z ↦ (@inv118_fa411fc9f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 1629 `x = (x ◇ x) ◇ ((x ◇ x) ◇ x)` holds of the term `x □ y := (x ◇ y) ◇ x` over any
finite magma satisfying equation 118 `x = y ◇ ((x ◇ y) ◇ y)`. -/
private theorem aux118_1629 [Finite G] [Magma G] (h : Equation118 G) (x : G) :
    x = (((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ x) := by
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
      x ≠ (((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ x) := mod_symm nh
  have ef14 : x ≠ ((x ◇ x) ◇ x) ◇ x := by
    first | exact superpose ef8 ef10 | exact superpose ef10 ef8
  subsumption ef14 ef9

theorem Equation1629_termStructuralFromFin_Equation118 :
    Law1629.TermStructuralFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law1629.models_iff]
    exact fun x ↦ @aux118_1629 G _ M h x
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (Term.var 1))), funext fun z ↦ (@inv118_e9e004b8f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 1685 `x = (y ◇ x) ◇ ((x ◇ y) ◇ y)` holds of the term `x □ y := (y ◇ x) ◇ y` over any
finite magma satisfying equation 118 `x = y ◇ ((x ◇ y) ◇ y)`. -/
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

theorem Equation1685_termStructuralFromFin_Equation118 :
    Law1685.TermStructuralFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1685.models_iff]
    exact fun x y ↦ @aux118_1685 G _ M h x y
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 0)), funext fun z ↦ (@inv118_fa411fc9f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 1692 `x = (y ◇ x) ◇ ((y ◇ x) ◇ y)` holds of the term `x □ y := (x ◇ y) ◇ x` over any
finite magma satisfying equation 118 `x = y ◇ ((x ◇ y) ◇ y)`. -/
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

theorem Equation1692_termStructuralFromFin_Equation118 :
    Law1692.TermStructuralFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law1692.models_iff]
    exact fun x y ↦ @aux118_1692 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (Term.var 1))), funext fun z ↦ (@inv118_e9e004b8f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3253 `x ◇ x = x ◇ (x ◇ (x ◇ x))` holds of the term `x □ y := (y ◇ x) ◇ y` over any
finite magma satisfying equation 118 `x = y ◇ ((x ◇ y) ◇ y)`. -/
private theorem aux118_3253 [Finite G] [Magma G] (h : Equation118 G) (x : G) :
    (x ◇ x) ◇ x = (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef10 :
      (x ◇ x) ◇ x ≠ (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) := mod_symm nh
  have ef13 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := superpose ef8 ef8
  have ef18 : (x ◇ x) ◇ x ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef19 : (x ◇ x) ◇ x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))) := by
    first | exact superpose ef13 ef18 | exact superpose ef18 ef13
  have ef21 : (x ◇ x) ◇ x ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef7 ef19 | exact superpose ef19 ef7
  subsumption ef21 ef13

theorem Equation3253_termStructuralFromFin_Equation118 :
    Law3253.TermStructuralFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3253.models_iff]
    exact fun x ↦ @aux118_3253 G _ M h x
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 0)), funext fun z ↦ (@inv118_fa411fc9f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3319 `x ◇ y = x ◇ (y ◇ (y ◇ y))` holds of the term `x □ y := (y ◇ x) ◇ y` over any
finite magma satisfying equation 118 `x = y ◇ ((x ◇ y) ◇ y)`. -/
private theorem aux118_3319 [Finite G] [Magma G] (h : Equation118 G) (x y : G) :
    (y ◇ x) ◇ y = (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ x) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef10 :
      (y ◇ x) ◇ y ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ x) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) := mod_symm nh
  have ef13 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := superpose ef8 ef8
  have ef17 : (y ◇ x) ◇ y ≠ ((y ◇ ((y ◇ y) ◇ y)) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ y)) := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef19 : (y ◇ x) ◇ y ≠ (y ◇ ((y ◇ y) ◇ y)) ◇ (x ◇ (y ◇ ((y ◇ y) ◇ y))) := by
    first | exact superpose ef13 ef17 | exact superpose ef17 ef13
  have ef21 : (y ◇ x) ◇ y ≠ y ◇ (x ◇ y) := by
    first | exact superpose ef7 ef19 | exact superpose ef19 ef7
  subsumption ef21 ef13

theorem Equation3319_termStructuralFromFin_Equation118 :
    Law3319.TermStructuralFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3319.models_iff]
    exact fun x y ↦ @aux118_3319 G _ M h x y
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 0)), funext fun z ↦ (@inv118_fa411fc9f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3456 `x ◇ x = x ◇ ((x ◇ x) ◇ x)` holds of the term `x □ y := (x ◇ y) ◇ x` over any
finite magma satisfying equation 118 `x = y ◇ ((x ◇ y) ◇ y)`. -/
private theorem aux118_3456 [Finite G] [Magma G] (h : Equation118 G) (x : G) :
    (x ◇ x) ◇ x = (x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef10 : (x ◇ x) ◇ x ≠ (x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x := mod_symm nh
  have ef13 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := superpose ef8 ef8
  have ef18 : (x ◇ x) ◇ x ≠ (x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef19 : (x ◇ x) ◇ x ≠ x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x) := by
    first | exact superpose ef13 ef18 | exact superpose ef18 ef13
  have ef21 : (x ◇ x) ◇ x ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef8 ef19 | exact superpose ef19 ef8
  subsumption ef21 ef13

theorem Equation3456_termStructuralFromFin_Equation118 :
    Law3456.TermStructuralFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law3456.models_iff]
    exact fun x ↦ @aux118_3456 G _ M h x
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (Term.var 1))), funext fun z ↦ (@inv118_e9e004b8f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3522 `x ◇ y = x ◇ ((y ◇ y) ◇ y)` holds of the term `x □ y := (x ◇ y) ◇ x` over any
finite magma satisfying equation 118 `x = y ◇ ((x ◇ y) ◇ y)`. -/
private theorem aux118_3522 [Finite G] [Magma G] (h : Equation118 G) (x y : G) :
    (x ◇ y) ◇ x = (x ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ x := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef10 : (x ◇ y) ◇ x ≠ (x ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ x := mod_symm nh
  have ef13 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := superpose ef8 ef8
  have ef18 : (x ◇ y) ◇ x ≠ (x ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef19 : (x ◇ y) ◇ x ≠ x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x) := by
    first | exact superpose ef13 ef18 | exact superpose ef18 ef13
  have ef21 : (x ◇ y) ◇ x ≠ x ◇ (y ◇ x) := by
    first | exact superpose ef7 ef19 | exact superpose ef19 ef7
  subsumption ef21 ef13

theorem Equation3522_termStructuralFromFin_Equation118 :
    Law3522.TermStructuralFromFin Law118 := by
  intro G _ M hGL
  have h : Equation118 G := Law118.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law3522.models_iff]
    exact fun x y ↦ @aux118_3522 G _ M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (Term.var 1))), funext fun z ↦ (@inv118_e9e004b8f G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := (y ◇ x) ◇ y` of equation 125 `x = y ◇ ((y ◇ x) ◇ y)` can be undone:
the operation is recovered as `x ◇ y = (x ◇ y) ◇ y` read in `□`. -/
private theorem inv125_fa411fc9 [Magma G] (h : Equation125 G) (x y : G) :
    (y ◇ ((y ◇ x) ◇ y)) ◇ y = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef6 : (y ◇ ((y ◇ x) ◇ y)) ◇ y ≠ x ◇ y := mod_symm nh
  have ef8 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  exact absurd rfl ef8

/-- Equation 8 `x = x ◇ (x ◇ x)` holds of the term `x □ y := (y ◇ x) ◇ y` over any magma satisfying
equation 125 `x = y ◇ ((y ◇ x) ◇ y)`. -/
private theorem aux125_8 [Magma G] (h : Equation125 G) (x : G) :
    x = (((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef6 : x ≠ (((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x) := mod_symm nh
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ X1 = X1 ◇ (X0 ◇ X1) := superpose ef5 ef5
  have ef10 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef13 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef14 : x ≠ (x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef7 ef13 | exact superpose ef13 ef7
  have ef17 : x ≠ (x ◇ (x ◇ x)) ◇ x := by
    first | exact superpose ef10 ef14 | exact superpose ef14 ef10
  have ef19 : x ≠ x ◇ ((x ◇ x) ◇ x) := by
    first | exact superpose ef7 ef17 | exact superpose ef17 ef7
  subsumption ef19 ef5

theorem Equation8_termStructuralFrom_Equation125 :
    Law8.TermStructuralFrom Law125 := by
  intro G M hGL
  have h : Equation125 G := Law125.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law8.models_iff]
    exact fun x ↦ @aux125_8 G M h x
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv125_fa411fc9 G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := (x ◇ y) ◇ x` of equation 125 `x = y ◇ ((y ◇ x) ◇ y)` can be undone:
the operation is recovered as `x ◇ y = y ◇ (y ◇ x)` read in `□`. -/
private theorem inv125_e9e004b8 [Magma G] (h : Equation125 G) (x y : G) :
    (y ◇ ((y ◇ x) ◇ y)) ◇ y = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef6 : (y ◇ ((y ◇ x) ◇ y)) ◇ y ≠ x ◇ y := mod_symm nh
  have ef8 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  exact absurd rfl ef8

/-- Equation 63 `x = y ◇ (x ◇ (x ◇ y))` holds of the term `x □ y := (x ◇ y) ◇ x` over any magma
satisfying equation 125 `x = y ◇ ((y ◇ x) ◇ y)`. -/
private theorem aux125_63 [Magma G] (h : Equation125 G) (x y : G) :
    x = (y ◇ ((x ◇ ((x ◇ y) ◇ x)) ◇ x)) ◇ y := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef6 : x ≠ (y ◇ ((x ◇ ((x ◇ y) ◇ x)) ◇ x)) ◇ y := mod_symm nh
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ X1 = X1 ◇ (X0 ◇ X1) := superpose ef5 ef5
  have ef8 : x ≠ (y ◇ (y ◇ x)) ◇ y := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  have ef14 : x ≠ y ◇ ((y ◇ x) ◇ y) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  subsumption ef14 ef5

theorem Equation63_termStructuralFrom_Equation125 :
    Law63.TermStructuralFrom Law125 := by
  intro G M hGL
  have h : Equation125 G := Law125.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law63.models_iff]
    exact fun x y ↦ @aux125_63 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv125_e9e004b8 G M h (z 0) (z 1)).symm⟩

/-- Equation 411 `x = x ◇ (x ◇ (x ◇ (x ◇ x)))` holds of the term `x □ y := (y ◇ x) ◇ y` over any
magma satisfying equation 125 `x = y ◇ ((y ◇ x) ◇ y)`. -/
private theorem aux125_411 [Magma G] (h : Equation125 G) (x : G) :
    x =
      (((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇
      x) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) := mod_symm nh
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ X1 = X1 ◇ (X0 ◇ X1) := superpose ef5 ef5
  have ef10 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef15 :
      x ≠ ((((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇
      x) ◇ (((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x) ◇
      (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef16 :
      x ≠ (((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) ◇
      (x ◇
      (((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef7 ef15 | exact superpose ef15 ef7
  have ef21 :
      x ≠ ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))))) ◇
      (x ◇
      ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))))) := by
    first | exact superpose ef7 ef16 | exact superpose ef16 ef7
  have ef25 :
      x ≠ (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (x ◇
      (((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x))))))) := by
    first | exact superpose ef7 ef21 | exact superpose ef21 ef7
  have ef29 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      (x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) := by
    first | exact superpose ef10 ef25 | exact superpose ef25 ef10
  have ef33 : x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ x))) := by
    first | exact superpose ef5 ef29 | exact superpose ef29 ef5
  have ef37 : x ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x)) ◇ (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x))) := by
    first | exact superpose ef7 ef33 | exact superpose ef33 ef7
  have ef41 : x ≠ (x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef5 ef37 | exact superpose ef37 ef5
  have ef45 : x ≠ (x ◇ (x ◇ x)) ◇ x := by
    first | exact superpose ef10 ef41 | exact superpose ef41 ef10
  have ef49 : x ≠ x ◇ ((x ◇ x) ◇ x) := by
    first | exact superpose ef7 ef45 | exact superpose ef45 ef7
  subsumption ef49 ef5

theorem Equation411_termStructuralFrom_Equation125 :
    Law411.TermStructuralFrom Law125 := by
  intro G M hGL
  have h : Equation125 G := Law125.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law411.models_iff]
    exact fun x ↦ @aux125_411 G M h x
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv125_fa411fc9 G M h (z 0) (z 1)).symm⟩

/-- Equation 1020 `x = x ◇ ((x ◇ (x ◇ x)) ◇ x)` holds of the term `x □ y := (y ◇ x) ◇ y` over any
magma satisfying equation 125 `x = y ◇ ((y ◇ x) ◇ y)`. -/
private theorem aux125_1020 [Magma G] (h : Equation125 G) (x : G) :
    x = (((x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      ((x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      ((x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x) := mod_symm nh
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ X1 = X1 ◇ (X0 ◇ X1) := superpose ef5 ef5
  have ef10 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef15 :
      x ≠ ((x ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ x) ◇
      (x ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef16 :
      x ≠ (x ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      (x ◇ (x ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x))) := by
    first | exact superpose ef7 ef15 | exact superpose ef15 ef7
  have ef21 :
      x ≠ (x ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef10 ef16 | exact superpose ef16 ef10
  have ef25 :
      x ≠ (x ◇ ((((x ◇ x) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x)) ◇
      (((x ◇ x) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) := by
    first | exact superpose ef7 ef21 | exact superpose ef21 ef7
  have ef29 : x ≠ (x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x) := by
    first | exact superpose ef5 ef25 | exact superpose ef25 ef5
  have ef33 : x ≠ (x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x) := by
    first | exact superpose ef7 ef29 | exact superpose ef29 ef7
  have ef37 : x ≠ (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef7 ef33 | exact superpose ef33 ef7
  have ef41 : x ≠ (x ◇ (x ◇ x)) ◇ x := by
    first | exact superpose ef5 ef37 | exact superpose ef37 ef5
  have ef45 : x ≠ x ◇ ((x ◇ x) ◇ x) := by
    first | exact superpose ef7 ef41 | exact superpose ef41 ef7
  subsumption ef45 ef5

theorem Equation1020_termStructuralFrom_Equation125 :
    Law1020.TermStructuralFrom Law125 := by
  intro G M hGL
  have h : Equation125 G := Law125.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1020.models_iff]
    exact fun x ↦ @aux125_1020 G M h x
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv125_fa411fc9 G M h (z 0) (z 1)).symm⟩

/-- Equation 1629 `x = (x ◇ x) ◇ ((x ◇ x) ◇ x)` holds of the term `x □ y := (x ◇ y) ◇ x` over any
magma satisfying equation 125 `x = y ◇ ((y ◇ x) ◇ y)`. -/
private theorem aux125_1629 [Magma G] (h : Equation125 G) (x : G) :
    x = (((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ x) := mod_symm nh
  have ef8 : x ≠ x ◇ ((x ◇ x) ◇ x) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  subsumption ef8 ef5

theorem Equation1629_termStructuralFrom_Equation125 :
    Law1629.TermStructuralFrom Law125 := by
  intro G M hGL
  have h : Equation125 G := Law125.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law1629.models_iff]
    exact fun x ↦ @aux125_1629 G M h x
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv125_e9e004b8 G M h (z 0) (z 1)).symm⟩

/-- Equation 1685 `x = (y ◇ x) ◇ ((x ◇ y) ◇ y)` holds of the term `x □ y := (y ◇ x) ◇ y` over any
magma satisfying equation 125 `x = y ◇ ((y ◇ x) ◇ y)`. -/
private theorem aux125_1685 [Magma G] (h : Equation125 G) (x y : G) :
    x = (((y ◇ ((y ◇ x) ◇ y)) ◇ y) ◇ ((x ◇ y) ◇ x)) ◇ ((y ◇ ((y ◇ x) ◇ y)) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((y ◇ ((y ◇ x) ◇ y)) ◇ y) ◇ ((x ◇ y) ◇ x)) ◇ ((y ◇ ((y ◇ x) ◇ y)) ◇ y) := mod_symm nh
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ X1 = X1 ◇ (X0 ◇ X1) := superpose ef5 ef5
  have ef8 : x ≠ ((x ◇ y) ◇ ((x ◇ y) ◇ x)) ◇ (x ◇ y) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  have ef14 : x ≠ (x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (x ◇ y)) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  subsumption ef14 ef5

theorem Equation1685_termStructuralFrom_Equation125 :
    Law1685.TermStructuralFrom Law125 := by
  intro G M hGL
  have h : Equation125 G := Law125.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1685.models_iff]
    exact fun x y ↦ @aux125_1685 G M h x y
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv125_fa411fc9 G M h (z 0) (z 1)).symm⟩

/-- Equation 1692 `x = (y ◇ x) ◇ ((y ◇ x) ◇ y)` holds of the term `x □ y := (x ◇ y) ◇ x` over any
magma satisfying equation 125 `x = y ◇ ((y ◇ x) ◇ y)`. -/
private theorem aux125_1692 [Magma G] (h : Equation125 G) (x y : G) :
    x = (((y ◇ x) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇ ((y ◇ x) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((y ◇ x) ◇ y) ◇ ((((y ◇ x) ◇ y) ◇ y) ◇ ((y ◇ x) ◇ y))) ◇ ((y ◇ x) ◇ y) := mod_symm nh
  have ef8 : x ≠ y ◇ ((y ◇ x) ◇ y) := by
    first | exact superpose ef5 ef6 | exact superpose ef6 ef5
  subsumption ef8 ef5

theorem Equation1692_termStructuralFrom_Equation125 :
    Law1692.TermStructuralFrom Law125 := by
  intro G M hGL
  have h : Equation125 G := Law125.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law1692.models_iff]
    exact fun x y ↦ @aux125_1692 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv125_e9e004b8 G M h (z 0) (z 1)).symm⟩

/-- Equation 3253 `x ◇ x = x ◇ (x ◇ (x ◇ x))` holds of the term `x □ y := (y ◇ x) ◇ y` over any
magma satisfying equation 125 `x = y ◇ ((y ◇ x) ◇ y)`. -/
private theorem aux125_3253 [Magma G] (h : Equation125 G) (x : G) :
    (x ◇ x) ◇ x = (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef6 :
      (x ◇ x) ◇ x ≠ (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) := mod_symm nh
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ X1 = X1 ◇ (X0 ◇ X1) := superpose ef5 ef5
  have ef10 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef14 :
      x ◇ (x ◇ x) ≠ ((((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇ x) ◇
      (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef15 :
      x ◇ (x ◇ x) ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x))) ◇
      (x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef7 ef14 | exact superpose ef14 ef7
  have ef19 :
      x ◇ (x ◇ x) ≠ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef7 ef15 | exact superpose ef15 ef7
  have ef22 : x ◇ (x ◇ x) ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef10 ef19 | exact superpose ef19 ef10
  have ef25 : x ◇ (x ◇ x) ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ x) := by
    first | exact superpose ef5 ef22 | exact superpose ef22 ef5
  have ef28 : x ◇ (x ◇ x) ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ x) := by
    first | exact superpose ef7 ef25 | exact superpose ef25 ef7
  have ef31 : x ◇ (x ◇ x) ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef5 ef28 | exact superpose ef28 ef5
  exact absurd rfl ef31

theorem Equation3253_termStructuralFrom_Equation125 :
    Law3253.TermStructuralFrom Law125 := by
  intro G M hGL
  have h : Equation125 G := Law125.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3253.models_iff]
    exact fun x ↦ @aux125_3253 G M h x
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv125_fa411fc9 G M h (z 0) (z 1)).symm⟩

/-- Equation 3319 `x ◇ y = x ◇ (y ◇ (y ◇ y))` holds of the term `x □ y := (y ◇ x) ◇ y` over any
magma satisfying equation 125 `x = y ◇ ((y ◇ x) ◇ y)`. -/
private theorem aux125_3319 [Magma G] (h : Equation125 G) (x y : G) :
    (y ◇ x) ◇ y = (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ x) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef6 :
      (y ◇ x) ◇ y ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ x) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) := mod_symm nh
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ X1 = X1 ◇ (X0 ◇ X1) := superpose ef5 ef5
  have ef12 :
      (y ◇ x) ◇ y ≠ ((((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) ◇ x) ◇
      (((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef13 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef15 :
      (y ◇ x) ◇ y ≠ (((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) ◇
      (x ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y)))) := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  have ef19 :
      (y ◇ x) ◇ y ≠ ((y ◇ (y ◇ y)) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ ((y ◇ (y ◇ y)) ◇ (y ◇ (y ◇ (y ◇ y))))) := by
    first | exact superpose ef7 ef15 | exact superpose ef15 ef7
  have ef22 : (y ◇ x) ◇ y ≠ ((y ◇ (y ◇ y)) ◇ y) ◇ (x ◇ ((y ◇ (y ◇ y)) ◇ y)) := by
    first | exact superpose ef13 ef19 | exact superpose ef19 ef13
  have ef25 : (y ◇ x) ◇ y ≠ (y ◇ ((y ◇ y) ◇ y)) ◇ (x ◇ (y ◇ ((y ◇ y) ◇ y))) := by
    first | exact superpose ef7 ef22 | exact superpose ef22 ef7
  have ef28 : (y ◇ x) ◇ y ≠ y ◇ (x ◇ y) := by
    first | exact superpose ef5 ef25 | exact superpose ef25 ef5
  subsumption ef28 ef7

theorem Equation3319_termStructuralFrom_Equation125 :
    Law3319.TermStructuralFrom Law125 := by
  intro G M hGL
  have h : Equation125 G := Law125.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op y x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3319.models_iff]
    exact fun x y ↦ @aux125_3319 G M h x y
  · exact ⟨(tm (tm (Term.var 1) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)), funext fun z ↦ (@inv125_fa411fc9 G M h (z 0) (z 1)).symm⟩

/-- Equation 3456 `x ◇ x = x ◇ ((x ◇ x) ◇ x)` holds of the term `x □ y := (x ◇ y) ◇ x` over any
magma satisfying equation 125 `x = y ◇ ((y ◇ x) ◇ y)`. -/
private theorem aux125_3456 [Magma G] (h : Equation125 G) (x : G) :
    (x ◇ x) ◇ x = (x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef6 : (x ◇ x) ◇ x ≠ (x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ x := mod_symm nh
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ X1 = X1 ◇ (X0 ◇ X1) := superpose ef5 ef5
  have ef14 : (x ◇ x) ◇ x ≠ x ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef15 : (x ◇ x) ◇ x ≠ x ◇ ((((x ◇ x) ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x) := by
    first | exact superpose ef7 ef14 | exact superpose ef14 ef7
  have ef19 : (x ◇ x) ◇ x ≠ x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ x) := by
    first | exact superpose ef5 ef15 | exact superpose ef15 ef5
  have ef22 : x ◇ (x ◇ x) ≠ x ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ x) := by
    first | exact superpose ef7 ef19 | exact superpose ef19 ef7
  have ef25 : x ◇ (x ◇ x) ≠ x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x) := by
    first | exact superpose ef7 ef22 | exact superpose ef22 ef7
  have ef28 : (x ◇ x) ◇ x ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef5 ef25 | exact superpose ef25 ef5
  subsumption ef28 ef7

theorem Equation3456_termStructuralFrom_Equation125 :
    Law3456.TermStructuralFrom Law125 := by
  intro G M hGL
  have h : Equation125 G := Law125.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law3456.models_iff]
    exact fun x ↦ @aux125_3456 G M h x
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv125_e9e004b8 G M h (z 0) (z 1)).symm⟩

/-- Equation 3522 `x ◇ y = x ◇ ((y ◇ y) ◇ y)` holds of the term `x □ y := (x ◇ y) ◇ x` over any
magma satisfying equation 125 `x = y ◇ ((y ◇ x) ◇ y)`. -/
private theorem aux125_3522 [Magma G] (h : Equation125 G) (x y : G) :
    (x ◇ y) ◇ x = (x ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ x := by
  by_contra nh
  have ef5 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef6 : (x ◇ y) ◇ x ≠ (x ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ x := mod_symm nh
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ X1 = X1 ◇ (X0 ◇ X1) := superpose ef5 ef5
  have ef10 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef14 : (x ◇ y) ◇ x ≠ (x ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y)))) ◇ x := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef15 : (x ◇ y) ◇ x ≠ x ◇ ((((y ◇ (y ◇ y)) ◇ y) ◇ (y ◇ (y ◇ y))) ◇ x) := by
    first | exact superpose ef7 ef14 | exact superpose ef14 ef7
  have ef19 : (x ◇ y) ◇ x ≠ x ◇ (((y ◇ (y ◇ y)) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ x) := by
    first | exact superpose ef7 ef15 | exact superpose ef15 ef7
  have ef22 : (x ◇ y) ◇ x ≠ x ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ x) := by
    first | exact superpose ef10 ef19 | exact superpose ef19 ef10
  have ef25 : (x ◇ y) ◇ x ≠ x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ x) := by
    first | exact superpose ef7 ef22 | exact superpose ef22 ef7
  have ef28 : (x ◇ y) ◇ x ≠ x ◇ (y ◇ x) := by
    first | exact superpose ef5 ef25 | exact superpose ef25 ef5
  subsumption ef28 ef7

theorem Equation3522_termStructuralFrom_Equation125 :
    Law3522.TermStructuralFrom Law125 := by
  intro G M hGL
  have h : Equation125 G := Law125.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law3522.models_iff]
    exact fun x y ↦ @aux125_3522 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv125_e9e004b8 G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := (x ◇ x) ◇ (y ◇ x)` of equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))` can
be undone: the operation is recovered as `x ◇ y = x ◇ (x ◇ (x ◇ y))` read in `□`. -/
private theorem inv546_dba7a67e [Magma G] (h : Equation546 G) (x y : G) :
    (x ◇ x) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ x) = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 : (x ◇ x) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ x) ≠ x ◇ y := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef11 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef12 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef82 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef142 : x ◇ y ≠ (x ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ x))) ◇ x) := by
    first | exact superpose ef11 ef6 | exact superpose ef6 ef11
  have ef164 : x ◇ y ≠ x ◇ ((x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ x))) ◇ (x ◇ x)) := by
    first | exact superpose ef11 ef142 | exact superpose ef142 ef11
  have ef177 : x ◇ y ≠ x ◇ (x ◇ ((x ◇ x) ◇ (y ◇ x))) := by
    first | exact superpose ef82 ef164 | exact superpose ef164 ef82
  have ef185 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef12 ef177 | exact superpose ef177 ef12
  exact absurd rfl ef185

/-- Equation 43 `x ◇ y = y ◇ x` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over any magma
satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_43 [Magma G] (h : Equation546 G) (x y : G) :
    (x ◇ x) ◇ (y ◇ x) = (y ◇ y) ◇ (x ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 : (x ◇ x) ◇ (y ◇ x) ≠ (y ◇ y) ◇ (x ◇ y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef11 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef13 (X0 X1 X2 X3 : G) : (X1 ◇ X0) ◇ (X2 ◇ X1) = X3 ◇ (X0 ◇ (X3 ◇ X2)) := by
    first | exact superpose ef5 ef8 | exact superpose ef8 ef5
  have ef26 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X1 ◇ X0)) = X3 ◇ (X0 ◇ (X3 ◇ X2)) := by
    first | exact superpose ef11 ef13 | exact superpose ef13 ef11
  have ef139 : (x ◇ x) ◇ (y ◇ x) ≠ y ◇ (x ◇ (y ◇ y)) := by
    first | exact superpose ef11 ef6 | exact superpose ef6 ef11
  have ef159 : y ◇ (x ◇ (y ◇ y)) ≠ x ◇ (y ◇ (x ◇ x)) := by
    first | exact superpose ef11 ef139 | exact superpose ef139 ef11
  subsumption ef159 ef26

theorem Equation43_termStructuralFrom_Equation546 :
    Law43.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law43.models_iff]
    exact fun x y ↦ @aux546_43 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 427 `x = x ◇ (y ◇ (x ◇ (x ◇ y)))` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_427 [Magma G] (h : Equation546 G) (x y : G) :
    x = (x ◇ x) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ y)) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ x) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ y)) ◇ x) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef161 : x ≠ (x ◇ x) ◇ ((y ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ (y ◇ y))) ◇ x) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef166 : x ≠ x ◇ ((y ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ (y ◇ y))) ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef161 | exact superpose ef161 ef12
  have ef183 : x ≠ y ◇ (x ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x))) := by
    first | exact superpose ef83 ef166 | exact superpose ef166 ef83
  have ef193 : x ≠ y ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇ x) := by
    first | exact superpose ef121 ef183 | exact superpose ef183 ef121
  have ef203 : x ≠ x ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇ y) := by
    first | exact superpose ef12 ef193 | exact superpose ef193 ef12
  have ef213 : x ≠ y ◇ ((x ◇ x) ◇ (y ◇ x)) := by
    first | exact superpose ef121 ef203 | exact superpose ef203 ef121
  have ef221 : x ≠ y ◇ (x ◇ (y ◇ (x ◇ x))) := by
    first | exact superpose ef12 ef213 | exact superpose ef213 ef12
  subsumption ef221 ef10

theorem Equation427_termStructuralFrom_Equation546 :
    Law427.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law427.models_iff]
    exact fun x y ↦ @aux546_427 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 511 `x = y ◇ (y ◇ (y ◇ (x ◇ y)))` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_511 [Magma G] (h : Equation546 G) (x y : G) :
    x = (y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)) ◇ y)) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)) ◇ y)) ◇ y) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef160 : x ≠ (y ◇ y) ◇ ((y ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)) ◇ (y ◇ y))) ◇ y) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef167 : x ≠ y ◇ ((y ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)) ◇ (y ◇ y))) ◇ (y ◇ y)) := by
    first | exact superpose ef12 ef160 | exact superpose ef160 ef12
  have ef184 : x ≠ y ◇ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y))) := by
    first | exact superpose ef83 ef167 | exact superpose ef167 ef83
  have ef194 : x ≠ y ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ y) ◇ y) := by
    first | exact superpose ef121 ef184 | exact superpose ef184 ef121
  have ef204 : x ≠ y ◇ ((x ◇ x) ◇ (y ◇ x)) := by
    first | exact superpose ef121 ef194 | exact superpose ef194 ef121
  have ef214 : x ≠ y ◇ (x ◇ (y ◇ (x ◇ x))) := by
    first | exact superpose ef12 ef204 | exact superpose ef204 ef12
  subsumption ef214 ef10

theorem Equation511_termStructuralFrom_Equation546 :
    Law511.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law511.models_iff]
    exact fun x y ↦ @aux546_511 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_556 [Magma G] (h : Equation546 G) (x y z : G) :
    x = (y ◇ y) ◇ (((z ◇ z) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y)) ◇ z)) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (y ◇ y) ◇ (((z ◇ z) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y)) ◇ z)) ◇ y) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef163 : x ≠ (y ◇ y) ◇ ((z ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y)) ◇ (z ◇ z))) ◇ y) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef165 : x ≠ y ◇ ((z ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y)) ◇ (z ◇ z))) ◇ (y ◇ y)) := by
    first | exact superpose ef12 ef163 | exact superpose ef163 ef12
  have ef183 : x ≠ z ◇ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y))) := by
    first | exact superpose ef83 ef165 | exact superpose ef165 ef83
  have ef193 : x ≠ z ◇ ((((x ◇ x) ◇ (z ◇ x)) ◇ y) ◇ y) := by
    first | exact superpose ef121 ef183 | exact superpose ef183 ef121
  have ef203 : x ≠ y ◇ ((((x ◇ x) ◇ (z ◇ x)) ◇ y) ◇ z) := by
    first | exact superpose ef12 ef193 | exact superpose ef193 ef12
  have ef213 : x ≠ z ◇ ((x ◇ x) ◇ (z ◇ x)) := by
    first | exact superpose ef121 ef203 | exact superpose ef203 ef121
  have ef221 : x ≠ z ◇ (x ◇ (z ◇ (x ◇ x))) := by
    first | exact superpose ef12 ef213 | exact superpose ef213 ef12
  subsumption ef221 ef10

theorem Equation556_termStructuralFrom_Equation546 :
    Law556.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law556.models_iff]
    exact fun x y z ↦ @aux546_556 G M h x y z
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 614 `x = x ◇ (x ◇ ((x ◇ x) ◇ x))` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_614 [Magma G] (h : Equation546 G) (x : G) :
    x = (x ◇ x) ◇
      (((x ◇ x) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ x)) ◇
      x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ x) ◇
      (((x ◇ x) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ x)) ◇
      x) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef120 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X1 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X3) := superpose ef12 ef12
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef150 :
      x ≠ (x ◇ x) ◇
      ((x ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x))) ◇
      x) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef172 :
      x ≠ x ◇
      ((x ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x))) ◇
      (x ◇ x)) := by
    first | exact superpose ef12 ef150 | exact superpose ef150 ef12
  have ef189 :
      x ≠ x ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x))))) := by
    first | exact superpose ef83 ef172 | exact superpose ef172 ef83
  have ef201 :
      x ≠ x ◇ (x ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))))) := by
    first | exact superpose ef120 ef189 | exact superpose ef189 ef120
  have ef213 : x ≠ x ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x)) := by
    first | exact superpose ef121 ef201 | exact superpose ef201 ef121
  have ef224 : x ≠ (x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x))) := by
    first | exact superpose ef83 ef213 | exact superpose ef213 ef83
  subsumption ef224 ef10

theorem Equation614_termStructuralFrom_Equation546 :
    Law614.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law614.models_iff]
    exact fun x ↦ @aux546_614 G M h x
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 632 `x = x ◇ (y ◇ ((x ◇ y) ◇ x))` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_632 [Magma G] (h : Equation546 G) (x y : G) :
    x = (x ◇ x) ◇
      (((y ◇ y) ◇ (((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ x)))) ◇ y)) ◇
      x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ x) ◇
      (((y ◇ y) ◇ (((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ x)))) ◇ y)) ◇
      x) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef16 (X0 X1 X2 X3 : G) : X3 ◇ X2 = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1) := superpose ef8 ef8
  have ef25 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  have ef28 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    first | exact superpose ef12 ef25 | exact superpose ef25 ef12
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef162 :
      x ≠ (x ◇ x) ◇
      (((y ◇ y) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇ y)) ◇
      x) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef170 :
      x ≠ x ◇
      (((y ◇ y) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇ y)) ◇
      (x ◇ x)) := by
    first | exact superpose ef12 ef162 | exact superpose ef162 ef12
  have ef190 :
      x ≠ x ◇ (x ◇ (x ◇ ((y ◇ y) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇ y)))) := by
    first | exact superpose ef12 ef170 | exact superpose ef170 ef12
  have ef202 :
      x ≠ x ◇ (x ◇ (x ◇ (y ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇ (y ◇ y))))) := by
    first | exact superpose ef12 ef190 | exact superpose ef190 ef12
  have ef214 : x ≠ x ◇ (x ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ x)))) := by
    first | exact superpose ef83 ef202 | exact superpose ef202 ef83
  have ef226 : x ≠ y ◇ ((x ◇ x) ◇ (y ◇ x)) := by
    first | exact superpose ef28 ef214 | exact superpose ef214 ef28
  have ef236 : x ≠ y ◇ (x ◇ (y ◇ (x ◇ x))) := by
    first | exact superpose ef12 ef226 | exact superpose ef226 ef12
  subsumption ef236 ef10

theorem Equation632_termStructuralFrom_Equation546 :
    Law632.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law632.models_iff]
    exact fun x y ↦ @aux546_632 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 639 `x = x ◇ (y ◇ ((y ◇ x) ◇ x))` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_639 [Magma G] (h : Equation546 G) (x y : G) :
    x = (x ◇ x) ◇
      (((y ◇ y) ◇ (((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇ y)) ◇
      x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ x) ◇
      (((y ◇ y) ◇ (((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇ y)) ◇
      x) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef16 (X0 X1 X2 X3 : G) : X3 ◇ X2 = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1) := superpose ef8 ef8
  have ef25 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  have ef28 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    first | exact superpose ef12 ef25 | exact superpose ef25 ef12
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef162 :
      x ≠ (x ◇ x) ◇
      (((y ◇ y) ◇ ((((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ y)) ◇
      x) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef170 :
      x ≠ x ◇
      (((y ◇ y) ◇ ((((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ y)) ◇
      (x ◇ x)) := by
    first | exact superpose ef12 ef162 | exact superpose ef162 ef12
  have ef190 :
      x ≠ x ◇ (x ◇ (x ◇ ((y ◇ y) ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ y)))) := by
    first | exact superpose ef12 ef170 | exact superpose ef170 ef12
  have ef202 :
      x ≠ x ◇ (x ◇ (x ◇ (y ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ (y ◇ y))))) := by
    first | exact superpose ef12 ef190 | exact superpose ef190 ef12
  have ef214 : x ≠ x ◇ (x ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ x)))) := by
    first | exact superpose ef83 ef202 | exact superpose ef202 ef83
  have ef226 : x ≠ y ◇ ((y ◇ y) ◇ (x ◇ y)) := by
    first | exact superpose ef28 ef214 | exact superpose ef214 ef28
  have ef236 : x ≠ (x ◇ y) ◇ y := by
    first | exact superpose ef121 ef226 | exact superpose ef226 ef121
  subsumption ef236 ef9

theorem Equation639_termStructuralFrom_Equation546 :
    Law639.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law639.models_iff]
    exact fun x y ↦ @aux546_639 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 667 `x = y ◇ (x ◇ ((x ◇ x) ◇ y))` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_667 [Magma G] (h : Equation546 G) (x y : G) :
    x = (y ◇ y) ◇
      (((x ◇ x) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ x)) ◇
      y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (y ◇ y) ◇
      (((x ◇ x) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ x)) ◇
      y) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef120 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X1 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X3) := superpose ef12 ef12
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef164 :
      x ≠ (y ◇ y) ◇
      ((x ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x))) ◇
      y) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef168 :
      x ≠ y ◇
      ((x ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x))) ◇
      (y ◇ y)) := by
    first | exact superpose ef12 ef164 | exact superpose ef164 ef12
  have ef188 :
      x ≠ x ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x))))) := by
    first | exact superpose ef83 ef168 | exact superpose ef168 ef83
  have ef200 :
      x ≠ x ◇ (y ◇ (((x ◇ x) ◇ y) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))))) := by
    first | exact superpose ef120 ef188 | exact superpose ef188 ef120
  have ef212 : x ≠ x ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x)) := by
    first | exact superpose ef121 ef200 | exact superpose ef200 ef121
  have ef224 : x ≠ (x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x))) := by
    first | exact superpose ef83 ef212 | exact superpose ef212 ef83
  subsumption ef224 ef10

theorem Equation667_termStructuralFrom_Equation546 :
    Law667.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law667.models_iff]
    exact fun x y ↦ @aux546_667 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 707 `x = y ◇ (y ◇ ((x ◇ y) ◇ y))` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_707 [Magma G] (h : Equation546 G) (x y : G) :
    x = (y ◇ y) ◇
      (((y ◇ y) ◇ (((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (y ◇ x)))) ◇ y)) ◇
      y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (y ◇ y) ◇
      (((y ◇ y) ◇ (((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (y ◇ x)))) ◇ y)) ◇
      y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef16 (X0 X1 X2 X3 : G) : X3 ◇ X2 = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1) := superpose ef8 ef8
  have ef25 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  have ef28 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    first | exact superpose ef12 ef25 | exact superpose ef25 ef12
  have ef162 :
      x ≠ (y ◇ y) ◇
      (((y ◇ y) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇ y)) ◇
      y) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef170 :
      x ≠ y ◇
      (((y ◇ y) ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇ y)) ◇
      (y ◇ y)) := by
    first | exact superpose ef12 ef162 | exact superpose ef162 ef12
  have ef190 :
      x ≠ y ◇ (y ◇ (y ◇ ((y ◇ y) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇ y)))) := by
    first | exact superpose ef12 ef170 | exact superpose ef170 ef12
  have ef202 :
      x ≠ (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇ (y ◇ y) := by
    first | exact superpose ef28 ef190 | exact superpose ef190 ef28
  have ef214 :
      x ≠ y ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))))) := by
    first | exact superpose ef12 ef202 | exact superpose ef202 ef12
  have ef226 : x ≠ y ◇ ((x ◇ x) ◇ (y ◇ x)) := by
    first | exact superpose ef10 ef214 | exact superpose ef214 ef10
  have ef236 : x ≠ y ◇ (x ◇ (y ◇ (x ◇ x))) := by
    first | exact superpose ef12 ef226 | exact superpose ef226 ef12
  subsumption ef236 ef10

theorem Equation707_termStructuralFrom_Equation546 :
    Law707.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law707.models_iff]
    exact fun x y ↦ @aux546_707 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_714 [Magma G] (h : Equation546 G) (x y : G) :
    x = (y ◇ y) ◇
      (((y ◇ y) ◇ (((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇ y)) ◇
      y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (y ◇ y) ◇
      (((y ◇ y) ◇ (((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇ y)) ◇
      y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef16 (X0 X1 X2 X3 : G) : X3 ◇ X2 = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1) := superpose ef8 ef8
  have ef25 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  have ef28 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    first | exact superpose ef12 ef25 | exact superpose ef25 ef12
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef160 :
      x ≠ (y ◇ y) ◇
      (((y ◇ y) ◇ ((((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ y)) ◇
      y) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef171 :
      x ≠ y ◇
      (((y ◇ y) ◇ ((((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ y)) ◇
      (y ◇ y)) := by
    first | exact superpose ef12 ef160 | exact superpose ef160 ef12
  have ef190 :
      x ≠ y ◇ (y ◇ (y ◇ ((y ◇ y) ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ y)))) := by
    first | exact superpose ef12 ef171 | exact superpose ef171 ef12
  have ef202 :
      x ≠ (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ (y ◇ y) := by
    first | exact superpose ef28 ef190 | exact superpose ef190 ef28
  have ef214 :
      x ≠ y ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))))) := by
    first | exact superpose ef12 ef202 | exact superpose ef202 ef12
  have ef226 : x ≠ y ◇ ((y ◇ y) ◇ (x ◇ y)) := by
    first | exact superpose ef10 ef214 | exact superpose ef214 ef10
  have ef236 : x ≠ (x ◇ y) ◇ y := by
    first | exact superpose ef121 ef226 | exact superpose ef226 ef121
  subsumption ef236 ef9

theorem Equation714_termStructuralFrom_Equation546 :
    Law714.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law714.models_iff]
    exact fun x y ↦ @aux546_714 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 1023 `x = x ◇ ((x ◇ (x ◇ y)) ◇ y)` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_1023 [Magma G] (h : Equation546 G) (x y : G) :
    x = (x ◇ x) ◇
      (((((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x))) ◇
      (y ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)))) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ x) ◇
      (((((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x))) ◇
      (y ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)))) ◇ x) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef160 :
      x ≠ (x ◇ x) ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇
      (y ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x))))) ◇
      x) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef171 :
      x ≠ x ◇ ((((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇
      (y ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x))))) ◇ (x ◇
      x)) := by
    first | exact superpose ef12 ef160 | exact superpose ef160 ef12
  have ef190 : x ≠ ((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x)) ◇ (x ◇ y) := by
    first | exact superpose ef83 ef171 | exact superpose ef171 ef83
  have ef202 : x ≠ y ◇ (x ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x))) := by
    first | exact superpose ef12 ef190 | exact superpose ef190 ef12
  have ef214 : x ≠ y ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇ x) := by
    first | exact superpose ef121 ef202 | exact superpose ef202 ef121
  have ef226 : x ≠ x ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ x) ◇ y) := by
    first | exact superpose ef12 ef214 | exact superpose ef214 ef12
  have ef236 : x ≠ y ◇ ((x ◇ x) ◇ (y ◇ x)) := by
    first | exact superpose ef121 ef226 | exact superpose ef226 ef121
  have ef246 : x ≠ y ◇ (x ◇ (y ◇ (x ◇ x))) := by
    first | exact superpose ef12 ef236 | exact superpose ef236 ef12
  subsumption ef246 ef10

theorem Equation1023_termStructuralFrom_Equation546 :
    Law1023.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law1023.models_iff]
    exact fun x y ↦ @aux546_1023 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 1109 `x = y ◇ ((y ◇ (x ◇ x)) ◇ x)` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_1109 [Magma G] (h : Equation546 G) (x y : G) :
    x = (y ◇ y) ◇
      (((((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y)) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y))) ◇
      (x ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y)))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (y ◇ y) ◇
      (((((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y)) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y))) ◇
      (x ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y)))) ◇ y) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef162 :
      x ≠ (y ◇ y) ◇ ((((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y)) ◇
      (x ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y)) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y))))) ◇
      y) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef170 :
      x ≠ y ◇ ((((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y)) ◇
      (x ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y)) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y))))) ◇ (y ◇
      y)) := by
    first | exact superpose ef12 ef162 | exact superpose ef162 ef12
  have ef190 : x ≠ ((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y)) ◇ (y ◇ x) := by
    first | exact superpose ef83 ef170 | exact superpose ef170 ef83
  have ef202 : x ≠ x ◇ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ y))) := by
    first | exact superpose ef12 ef190 | exact superpose ef190 ef12
  have ef214 : x ≠ x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ y) ◇ y) := by
    first | exact superpose ef121 ef202 | exact superpose ef202 ef121
  have ef226 : x ≠ x ◇ ((x ◇ x) ◇ (x ◇ x)) := by
    first | exact superpose ef9 ef214 | exact superpose ef214 ef9
  have ef236 : x ≠ (x ◇ x) ◇ x := by
    first | exact superpose ef121 ef226 | exact superpose ef226 ef121
  subsumption ef236 ef9

theorem Equation1109_termStructuralFrom_Equation546 :
    Law1109.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law1109.models_iff]
    exact fun x y ↦ @aux546_1109 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 1113 `x = y ◇ ((y ◇ (x ◇ y)) ◇ y)` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_1113 [Magma G] (h : Equation546 G) (x y : G) :
    x = (y ◇ y) ◇
      (((((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y))) ◇
      (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (y ◇ y) ◇
      (((((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y))) ◇
      (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)))) ◇ y) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef162 :
      x ≠ (y ◇ y) ◇ ((((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)) ◇
      (y ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y))))) ◇
      y) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef170 :
      x ≠ y ◇ ((((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)) ◇
      (y ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y))))) ◇ (y ◇
      y)) := by
    first | exact superpose ef12 ef162 | exact superpose ef162 ef12
  have ef190 : x ≠ ((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y)) ◇ (y ◇ y) := by
    first | exact superpose ef83 ef170 | exact superpose ef170 ef83
  have ef202 : x ≠ y ◇ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ y))) := by
    first | exact superpose ef12 ef190 | exact superpose ef190 ef12
  have ef214 : x ≠ y ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ y) ◇ y) := by
    first | exact superpose ef121 ef202 | exact superpose ef202 ef121
  have ef226 : x ≠ y ◇ ((x ◇ x) ◇ (y ◇ x)) := by
    first | exact superpose ef121 ef214 | exact superpose ef214 ef121
  have ef236 : x ≠ y ◇ (x ◇ (y ◇ (x ◇ x))) := by
    first | exact superpose ef12 ef226 | exact superpose ef226 ef12
  subsumption ef236 ef10

theorem Equation1113_termStructuralFrom_Equation546 :
    Law1113.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law1113.models_iff]
    exact fun x y ↦ @aux546_1113 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 1117 `x = y ◇ ((y ◇ (x ◇ z)) ◇ z)` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_1117 [Magma G] (h : Equation546 G) (x y z : G) :
    x = (y ◇ y) ◇
      (((((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y)) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y))) ◇
      (z ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y)))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (y ◇ y) ◇
      (((((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y)) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y))) ◇
      (z ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y)))) ◇ y) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef162 :
      x ≠ (y ◇ y) ◇ ((((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y)) ◇
      (z ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y)) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y))))) ◇
      y) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef170 :
      x ≠ y ◇ ((((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y)) ◇
      (z ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y)) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y))))) ◇ (y ◇
      y)) := by
    first | exact superpose ef12 ef162 | exact superpose ef162 ef12
  have ef190 : x ≠ ((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y)) ◇ (y ◇ z) := by
    first | exact superpose ef83 ef170 | exact superpose ef170 ef83
  have ef202 : x ≠ z ◇ (y ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ (z ◇ x)) ◇ y))) := by
    first | exact superpose ef12 ef190 | exact superpose ef190 ef12
  have ef214 : x ≠ z ◇ ((((x ◇ x) ◇ (z ◇ x)) ◇ y) ◇ y) := by
    first | exact superpose ef121 ef202 | exact superpose ef202 ef121
  have ef226 : x ≠ y ◇ ((((x ◇ x) ◇ (z ◇ x)) ◇ y) ◇ z) := by
    first | exact superpose ef12 ef214 | exact superpose ef214 ef12
  have ef236 : x ≠ z ◇ ((x ◇ x) ◇ (z ◇ x)) := by
    first | exact superpose ef121 ef226 | exact superpose ef226 ef121
  have ef246 : x ≠ z ◇ (x ◇ (z ◇ (x ◇ x))) := by
    first | exact superpose ef12 ef236 | exact superpose ef236 ef12
  subsumption ef246 ef10

theorem Equation1117_termStructuralFrom_Equation546 :
    Law1117.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law1117.models_iff]
    exact fun x y z ↦ @aux546_1117 G M h x y z
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 1223 `x = x ◇ (((x ◇ x) ◇ x) ◇ x)` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_1223 [Magma G] (h : Equation546 G) (x : G) :
    x = (x ◇ x) ◇ (((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))))) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ x) ◇ (((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))))) ◇
      x) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef120 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X1 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X3) := superpose ef12 ef12
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef151 :
      x ≠ (x ◇ x) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      (x ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x))))))) ◇ x) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef175 :
      x ≠ x ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x))))))) ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef151 | exact superpose ef151 ef12
  have ef194 :
      x ≠ ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x) := by
    first | exact superpose ef83 ef175 | exact superpose ef175 ef83
  have ef208 :
      x ≠ x ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x))))) := by
    first | exact superpose ef12 ef194 | exact superpose ef194 ef12
  have ef222 :
      x ≠ x ◇ (x ◇ (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))))) := by
    first | exact superpose ef120 ef208 | exact superpose ef208 ef120
  have ef235 : x ≠ x ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x)) := by
    first | exact superpose ef121 ef222 | exact superpose ef222 ef121
  have ef247 : x ≠ (x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x))) := by
    first | exact superpose ef83 ef235 | exact superpose ef235 ef83
  subsumption ef247 ef10

theorem Equation1223_termStructuralFrom_Equation546 :
    Law1223.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law1223.models_iff]
    exact fun x ↦ @aux546_1223 G M h x
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 1229 `x = x ◇ (((x ◇ y) ◇ x) ◇ y)` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_1229 [Magma G] (h : Equation546 G) (x y : G) :
    x = (x ◇ x) ◇ (((((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇ (y ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ x)))))) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ x) ◇ (((((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇ (y ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ x)))))) ◇
      x) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef16 (X0 X1 X2 X3 : G) : X3 ◇ X2 = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1) := superpose ef8 ef8
  have ef25 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  have ef28 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    first | exact superpose ef12 ef25 | exact superpose ef25 ef12
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef120 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X1 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X3) := superpose ef12 ef12
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef162 :
      x ≠ (x ◇ x) ◇ ((((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))))) ◇ (y ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))))) ◇ x) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef173 :
      x ≠ x ◇ ((((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))))) ◇ (y ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))))) ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef162 | exact superpose ef162 ef12
  have ef194 :
      x ≠ x ◇ (x ◇ (x ◇
      (((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))))) ◇ (y ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))))))) := by
    first | exact superpose ef12 ef173 | exact superpose ef173 ef12
  have ef208 :
      x ≠ x ◇ (x ◇ (x ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ y) ◇ ((x ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))))))))) := by
    first | exact superpose ef120 ef194 | exact superpose ef194 ef120
  have ef222 :
      x ≠ x ◇ (x ◇ (x ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ y) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇
      ((x ◇ x) ◇ (y ◇ x)))))) := by
    first | exact superpose ef121 ef208 | exact superpose ef208 ef121
  have ef236 :
      x ≠ x ◇ (x ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ y))))) := by
    first | exact superpose ef12 ef222 | exact superpose ef222 ef12
  have ef248 : x ≠ x ◇ (x ◇ (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ x)))) := by
    first | exact superpose ef83 ef236 | exact superpose ef236 ef83
  have ef260 : x ≠ y ◇ ((x ◇ x) ◇ (y ◇ x)) := by
    first | exact superpose ef28 ef248 | exact superpose ef248 ef28
  have ef272 : x ≠ y ◇ (x ◇ (y ◇ (x ◇ x))) := by
    first | exact superpose ef12 ef260 | exact superpose ef260 ef12
  subsumption ef272 ef10

theorem Equation1229_termStructuralFrom_Equation546 :
    Law1229.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law1229.models_iff]
    exact fun x y ↦ @aux546_1229 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 1239 `x = x ◇ (((y ◇ x) ◇ x) ◇ y)` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_1239 [Magma G] (h : Equation546 G) (x y : G) :
    x = (x ◇ x) ◇ (((((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ (y ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((y ◇ y) ◇ (x ◇ y)))))) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (x ◇ x) ◇ (((((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ (y ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (x ◇ ((y ◇ y) ◇ (x ◇ y)))))) ◇
      x) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef16 (X0 X1 X2 X3 : G) : X3 ◇ X2 = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1) := superpose ef8 ef8
  have ef25 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  have ef28 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    first | exact superpose ef12 ef25 | exact superpose ef25 ef12
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef120 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X1 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X3) := superpose ef12 ef12
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef164 :
      x ≠ (x ◇ x) ◇ ((((((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))))) ◇ (y ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))))) ◇ x) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef172 :
      x ≠ x ◇ ((((((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))))) ◇ (y ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))))) ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef164 | exact superpose ef164 ef12
  have ef194 :
      x ≠ x ◇ (x ◇ (x ◇
      (((((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))))) ◇ (y ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))))))) := by
    first | exact superpose ef12 ef172 | exact superpose ef172 ef12
  have ef208 :
      x ≠ x ◇ (x ◇ (x ◇ ((((y ◇ y) ◇ (x ◇ y)) ◇ y) ◇ ((x ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))))))))) := by
    first | exact superpose ef120 ef194 | exact superpose ef194 ef120
  have ef222 :
      x ≠ x ◇ (x ◇ (x ◇ ((((y ◇ y) ◇ (x ◇ y)) ◇ y) ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇
      ((y ◇ y) ◇ (x ◇ y)))))) := by
    first | exact superpose ef121 ef208 | exact superpose ef208 ef121
  have ef236 :
      x ≠ x ◇ (x ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ y))))) := by
    first | exact superpose ef12 ef222 | exact superpose ef222 ef12
  have ef248 : x ≠ x ◇ (x ◇ (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ x)))) := by
    first | exact superpose ef83 ef236 | exact superpose ef236 ef83
  have ef260 : x ≠ y ◇ ((y ◇ y) ◇ (x ◇ y)) := by
    first | exact superpose ef28 ef248 | exact superpose ef248 ef28
  have ef272 : x ≠ (x ◇ y) ◇ y := by
    first | exact superpose ef121 ef260 | exact superpose ef260 ef121
  subsumption ef272 ef9

theorem Equation1239_termStructuralFrom_Equation546 :
    Law1239.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law1239.models_iff]
    exact fun x y ↦ @aux546_1239 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 1278 `x = y ◇ (((x ◇ x) ◇ y) ◇ x)` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_1278 [Magma G] (h : Equation546 G) (x y : G) :
    x = (y ◇ y) ◇ (((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x)))))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (y ◇ y) ◇ (((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x)))))) ◇
      y) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef120 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X1 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X3) := superpose ef12 ef12
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef165 :
      x ≠ (y ◇ y) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      (x ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x))))))) ◇ y) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef171 :
      x ≠ y ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x))))))) ◇ (y ◇ y)) := by
    first | exact superpose ef12 ef165 | exact superpose ef165 ef12
  have ef193 :
      x ≠ ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (y ◇ x) := by
    first | exact superpose ef83 ef171 | exact superpose ef171 ef83
  have ef207 :
      x ≠ x ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (x ◇ x))))) := by
    first | exact superpose ef12 ef193 | exact superpose ef193 ef12
  have ef221 :
      x ≠ x ◇ (y ◇ (((x ◇ x) ◇ y) ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))))) := by
    first | exact superpose ef120 ef207 | exact superpose ef207 ef120
  have ef235 : x ≠ x ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x)) := by
    first | exact superpose ef121 ef221 | exact superpose ef221 ef121
  have ef247 : x ≠ (x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ (x ◇ x))) := by
    first | exact superpose ef83 ef235 | exact superpose ef235 ef83
  subsumption ef247 ef10

theorem Equation1278_termStructuralFrom_Equation546 :
    Law1278.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law1278.models_iff]
    exact fun x y ↦ @aux546_1278 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 1289 `x = y ◇ (((x ◇ y) ◇ y) ◇ y)` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_1289 [Magma G] (h : Equation546 G) (x y : G) :
    x = (y ◇ y) ◇ (((((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇ (y ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (y ◇ x)))))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (y ◇ y) ◇ (((((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇ (y ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ (y ◇ ((x ◇ x) ◇ (y ◇ x)))))) ◇
      y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef23 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X0)) = X3 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef24 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X0)))) = X3 := by
    first | exact superpose ef12 ef23 | exact superpose ef23 ef12
  have ef120 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X1 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X3) := superpose ef12 ef12
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef164 :
      x ≠ (y ◇ y) ◇ ((((((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))))) ◇ (y ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))))) ◇ y) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef172 :
      x ≠ y ◇ ((((((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))))) ◇ (y ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))))) ◇ (y ◇ y)) := by
    first | exact superpose ef12 ef164 | exact superpose ef164 ef12
  have ef194 :
      x ≠ y ◇ (y ◇ (y ◇
      (((((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))))) ◇ (y ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))))))) := by
    first | exact superpose ef12 ef172 | exact superpose ef172 ef12
  have ef208 :
      x ≠ y ◇ (y ◇ (y ◇ ((((x ◇ x) ◇ (y ◇ x)) ◇ y) ◇ ((y ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))))))))) := by
    first | exact superpose ef120 ef194 | exact superpose ef194 ef120
  have ef222 :
      x ≠ y ◇ (y ◇ (((y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))))) ◇ ((x ◇ x) ◇ (y ◇
      x)))) := by
    first | exact superpose ef121 ef208 | exact superpose ef208 ef121
  have ef236 :
      x ≠ y ◇ (y ◇ ((y ◇ (x ◇ x)) ◇ (x ◇ ((y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))) ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇
      (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))))))))) := by
    first | exact superpose ef120 ef222 | exact superpose ef222 ef120
  have ef248 :
      x ≠ y ◇ (y ◇ ((y ◇ (x ◇ x)) ◇ (x ◇
      ((((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))))) ◇
      ((x ◇ x) ◇ (y ◇ x)))))) := by
    first | exact superpose ef121 ef236 | exact superpose ef236 ef121
  have ef260 :
      x ≠ y ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))))) := by
    first | exact superpose ef24 ef248 | exact superpose ef248 ef24
  have ef272 : x ≠ y ◇ ((x ◇ x) ◇ (y ◇ x)) := by
    first | exact superpose ef10 ef260 | exact superpose ef260 ef10
  have ef284 : x ≠ y ◇ (x ◇ (y ◇ (x ◇ x))) := by
    first | exact superpose ef12 ef272 | exact superpose ef272 ef12
  subsumption ef284 ef10

theorem Equation1289_termStructuralFrom_Equation546 :
    Law1289.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law1289.models_iff]
    exact fun x y ↦ @aux546_1289 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 1316 `x = y ◇ (((y ◇ x) ◇ y) ◇ y)` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_1316 [Magma G] (h : Equation546 G) (x y : G) :
    x = (y ◇ y) ◇ (((((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ (y ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ y)))))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (y ◇ y) ◇ (((((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇ (y ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ y)))))) ◇
      y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef23 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X0)) = X3 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef24 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X0)))) = X3 := by
    first | exact superpose ef12 ef23 | exact superpose ef23 ef12
  have ef120 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X1 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X3) := superpose ef12 ef12
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef162 :
      x ≠ (y ◇ y) ◇ ((((((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))))) ◇ (y ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))))) ◇ y) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef173 :
      x ≠ y ◇ ((((((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))))) ◇ (y ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))))) ◇ (y ◇ y)) := by
    first | exact superpose ef12 ef162 | exact superpose ef162 ef12
  have ef194 :
      x ≠ y ◇ (y ◇ (y ◇
      (((((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))))) ◇ (y ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))))))) := by
    first | exact superpose ef12 ef173 | exact superpose ef173 ef12
  have ef208 :
      x ≠ y ◇ (y ◇ (y ◇ ((((y ◇ y) ◇ (x ◇ y)) ◇ y) ◇ ((y ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))))))))) := by
    first | exact superpose ef120 ef194 | exact superpose ef194 ef120
  have ef222 :
      x ≠ y ◇ (y ◇ (((y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))))) ◇ ((y ◇ y) ◇ (x ◇
      y)))) := by
    first | exact superpose ef121 ef208 | exact superpose ef208 ef121
  have ef236 :
      x ≠ y ◇ (y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇ ((y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))) ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇
      (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))))))))) := by
    first | exact superpose ef120 ef222 | exact superpose ef222 ef120
  have ef248 :
      x ≠ y ◇ (y ◇ ((x ◇ (y ◇ y)) ◇ (y ◇
      ((((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))))) ◇
      ((y ◇ y) ◇ (x ◇ y)))))) := by
    first | exact superpose ef121 ef236 | exact superpose ef236 ef121
  have ef260 :
      x ≠ y ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ (y ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))))) := by
    first | exact superpose ef24 ef248 | exact superpose ef248 ef24
  have ef272 : x ≠ y ◇ ((y ◇ y) ◇ (x ◇ y)) := by
    first | exact superpose ef10 ef260 | exact superpose ef260 ef10
  have ef284 : x ≠ (x ◇ y) ◇ y := by
    first | exact superpose ef121 ef272 | exact superpose ef272 ef121
  subsumption ef284 ef9

theorem Equation1316_termStructuralFrom_Equation546 :
    Law1316.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law1316.models_iff]
    exact fun x y ↦ @aux546_1316 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 4283 `x ◇ (x ◇ y) = x ◇ (y ◇ x)` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_4283 [Magma G] (h : Equation546 G) (x y : G) :
    (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) = (x ◇ x) ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ (x ◇ x) ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef16 (X0 X1 X2 X3 : G) : X3 ◇ X2 = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1) := superpose ef8 ef8
  have ef25 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  have ef28 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    first | exact superpose ef12 ef25 | exact superpose ef25 ef12
  have ef157 : (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef162 : (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ x ◇ (x ◇ (x ◇ ((y ◇ y) ◇ (x ◇ y)))) := by
    first | exact superpose ef12 ef157 | exact superpose ef157 ef12
  have ef175 : (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ x ◇ (x ◇ (x ◇ (y ◇ (x ◇ (y ◇ y))))) := by
    first | exact superpose ef12 ef162 | exact superpose ef162 ef12
  have ef181 : (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ x ◇ (x ◇ y) := by
    first | exact superpose ef10 ef175 | exact superpose ef175 ef10
  have ef187 : x ◇ (x ◇ y) ≠ x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef181 | exact superpose ef181 ef12
  have ef193 : x ◇ (x ◇ y) ≠ x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (y ◇ x)))) := by
    first | exact superpose ef12 ef187 | exact superpose ef187 ef12
  have ef197 : y ◇ (x ◇ x) ≠ x ◇ (x ◇ y) := by
    first | exact superpose ef28 ef193 | exact superpose ef193 ef28
  subsumption ef197 ef12

theorem Equation4283_termStructuralFrom_Equation546 :
    Law4283.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law4283.models_iff]
    exact fun x y ↦ @aux546_4283 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 4358 `x ◇ (y ◇ z) = x ◇ (z ◇ y)` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_4358 [Magma G] (h : Equation546 G) (x y z : G) :
    (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) = (x ◇ x) ◇ (((z ◇ z) ◇ (y ◇ z)) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ (x ◇ x) ◇ (((z ◇ z) ◇ (y ◇ z)) ◇ x) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
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
  have ef27 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X1 ◇ X0)) = X3 ◇ (X0 ◇ (X3 ◇ X2)) := by
    first | exact superpose ef12 ef14 | exact superpose ef14 ef12
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef156 : (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ (x ◇ x) ◇ ((z ◇ (y ◇ (z ◇ z))) ◇ x) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef163 : (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ x ◇ ((z ◇ (y ◇ (z ◇ z))) ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef156 | exact superpose ef156 ef12
  have ef176 : (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ z ◇ (x ◇ y) := by
    first | exact superpose ef83 ef163 | exact superpose ef163 ef83
  have ef182 : (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ y ◇ (x ◇ z) := by
    first | exact superpose ef12 ef176 | exact superpose ef176 ef12
  have ef188 : x ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ (x ◇ x)) ≠ y ◇ (x ◇ z) := by
    first | exact superpose ef12 ef182 | exact superpose ef182 ef12
  have ef194 : y ◇ (x ◇ z) ≠ x ◇ (x ◇ (x ◇ ((y ◇ y) ◇ (z ◇ y)))) := by
    first | exact superpose ef12 ef188 | exact superpose ef188 ef12
  have ef198 : y ◇ (x ◇ z) ≠ x ◇ (x ◇ (x ◇ (y ◇ (z ◇ (y ◇ y))))) := by
    first | exact superpose ef12 ef194 | exact superpose ef194 ef12
  have ef201 : y ◇ (x ◇ z) ≠ x ◇ (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z))))) := by
    first | exact superpose ef12 ef198 | exact superpose ef198 ef12
  have ef214 (X0 X1 X2 X3 : G) : X3 ◇ (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2 := by
    first | exact superpose ef7 ef20 | exact superpose ef20 ef7
  have ef215 (X0 X1 X2 X3 : G) : (X1 ◇ X0) ◇ X2 = X3 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1))) := by
    first | exact superpose ef5 ef20 | exact superpose ef20 ef5
  have ef1028 (X0 : G) : y ◇ (x ◇ z) ≠ x ◇ (x ◇ (x ◇ (X0 ◇ (z ◇ (X0 ◇ y))))) := by
    first | exact superpose ef27 ef201 | exact superpose ef201 ef27
  have ef1031 (X0 : G) : y ◇ (x ◇ z) ≠ ((z ◇ (X0 ◇ y)) ◇ x) ◇ X0 := by
    first | exact superpose ef215 ef1028 | exact superpose ef1028 ef215
  subsumption ef1031 ef214

theorem Equation4358_termStructuralFrom_Equation546 :
    Law4358.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law4358.models_iff]
    exact fun x y z ↦ @aux546_4358 G M h x y z
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 4380 `x ◇ (x ◇ x) = (x ◇ x) ◇ x` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_4380 [Magma G] (h : Equation546 G) (x : G) :
    (x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x) = (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (x ◇ ((x ◇ x) ◇ (x ◇ x))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      (x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x) ≠ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (x ◇ ((x ◇ x) ◇ (x ◇ x))) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef16 (X0 X1 X2 X3 : G) : X3 ◇ X2 = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1) := superpose ef8 ef8
  have ef25 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  have ef28 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    first | exact superpose ef12 ef25 | exact superpose ef25 ef12
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef146 :
      (x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x) ≠ ((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef168 : (x ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x) ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef28 ef146 | exact superpose ef146 ef28
  subsumption ef168 ef121

theorem Equation4380_termStructuralFrom_Equation546 :
    Law4380.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law4380.models_iff]
    exact fun x ↦ @aux546_4380 G M h x
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 4398 `x ◇ (x ◇ y) = (x ◇ y) ◇ x` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_4398 [Magma G] (h : Equation546 G) (x y : G) :
    (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) = (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇
      (x ◇ ((x ◇ x) ◇ (y ◇ x))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇
      (x ◇ ((x ◇ x) ◇ (y ◇ x))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef159 :
      (x ◇ x) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ x) ≠ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (y ◇ (x ◇ x)))) ◇
      (x ◇ (x ◇ (y ◇ (x ◇ x)))) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef164 :
      (x ◇ x) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ x) ≠ (x ◇ (y ◇ (x ◇ x))) ◇
      (x ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (y ◇ (x ◇ x))))) := by
    first | exact superpose ef12 ef159 | exact superpose ef159 ef12
  have ef179 : y ◇ (x ◇ x) ≠ (x ◇ x) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ x) := by
    first | exact superpose ef10 ef164 | exact superpose ef164 ef10
  have ef187 : y ◇ (x ◇ x) ≠ x ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef179 | exact superpose ef179 ef12
  have ef195 : y ◇ (x ◇ x) ≠ x ◇ (x ◇ y) := by
    first | exact superpose ef83 ef187 | exact superpose ef187 ef83
  subsumption ef195 ef12

theorem Equation4398_termStructuralFrom_Equation546 :
    Law4398.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law4398.models_iff]
    exact fun x y ↦ @aux546_4398 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 4405 `x ◇ (x ◇ y) = (y ◇ x) ◇ x` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_4405 [Magma G] (h : Equation546 G) (x y : G) :
    (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) = (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇
      (x ◇ ((y ◇ y) ◇ (x ◇ y))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇
      (x ◇ ((y ◇ y) ◇ (x ◇ y))) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef16 (X0 X1 X2 X3 : G) : X3 ◇ X2 = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1) := superpose ef8 ef8
  have ef23 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X0)) = X3 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef24 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X0)))) = X3 := by
    first | exact superpose ef12 ef23 | exact superpose ef23 ef12
  have ef25 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  have ef28 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    first | exact superpose ef12 ef25 | exact superpose ef25 ef12
  have ef120 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X1 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X3) := superpose ef12 ef12
  have ef158 :
      (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ ((y ◇ y) ◇ (x ◇ y)) ◇
      (x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ y)))) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef165 :
      (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ ((y ◇ y) ◇ (x ◇ y)) ◇
      (x ◇ ((x ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (x ◇ y))))) := by
    first | exact superpose ef12 ef158 | exact superpose ef158 ef12
  have ef180 :
      (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ ((x ◇ y) ◇ x) ◇
      (((y ◇ y) ◇ ((y ◇ y) ◇ (x ◇ y))) ◇ ((y ◇ y) ◇ (x ◇ y))) := by
    first | exact superpose ef120 ef165 | exact superpose ef165 ef120
  have ef188 :
      (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ ((x ◇ y) ◇ x) ◇
      ((x ◇ (y ◇ y)) ◇ (y ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (x ◇ y))))) := by
    first | exact superpose ef120 ef180 | exact superpose ef180 ef120
  have ef196 : (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ ((x ◇ y) ◇ x) ◇ (y ◇ y) := by
    first | exact superpose ef24 ef188 | exact superpose ef188 ef24
  have ef204 : (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ y ◇ (y ◇ ((x ◇ y) ◇ x)) := by
    first | exact superpose ef12 ef196 | exact superpose ef196 ef12
  have ef210 : (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ y ◇ (x ◇ ((x ◇ y) ◇ y)) := by
    first | exact superpose ef12 ef204 | exact superpose ef204 ef12
  have ef216 : (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ y ◇ (x ◇ x) := by
    first | exact superpose ef9 ef210 | exact superpose ef210 ef9
  have ef222 : (x ◇ x) ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ x) ≠ x ◇ (x ◇ y) := by
    first | exact superpose ef12 ef216 | exact superpose ef216 ef12
  have ef228 : x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ (x ◇ x)) ≠ x ◇ (x ◇ y) := by
    first | exact superpose ef12 ef222 | exact superpose ef222 ef12
  have ef233 : x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ (y ◇ x)))) ≠ x ◇ (x ◇ y) := by
    first | exact superpose ef12 ef228 | exact superpose ef228 ef12
  have ef237 : y ◇ (x ◇ x) ≠ x ◇ (x ◇ y) := by
    first | exact superpose ef28 ef233 | exact superpose ef233 ef28
  subsumption ef237 ef12

theorem Equation4405_termStructuralFrom_Equation546 :
    Law4405.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law4405.models_iff]
    exact fun x y ↦ @aux546_4405 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 4435 `x ◇ (y ◇ x) = (x ◇ y) ◇ x` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_4435 [Magma G] (h : Equation546 G) (x y : G) :
    (x ◇ x) ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ x) = (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇
      (x ◇ ((x ◇ x) ◇ (y ◇ x))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      (x ◇ x) ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ x) ≠ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x))) ◇
      (x ◇ ((x ◇ x) ◇ (y ◇ x))) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef16 (X0 X1 X2 X3 : G) : X3 ◇ X2 = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1) := superpose ef8 ef8
  have ef25 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  have ef28 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    first | exact superpose ef12 ef25 | exact superpose ef25 ef12
  have ef158 :
      (x ◇ x) ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ x) ≠ ((x ◇ x) ◇ (y ◇ x)) ◇
      (x ◇ (((x ◇ x) ◇ (y ◇ x)) ◇ ((x ◇ x) ◇ (y ◇ x)))) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef165 : (x ◇ x) ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ x) ≠ y ◇ (x ◇ x) := by
    first | exact superpose ef28 ef158 | exact superpose ef158 ef28
  have ef180 : (x ◇ x) ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ x) ≠ x ◇ (x ◇ y) := by
    first | exact superpose ef12 ef165 | exact superpose ef165 ef12
  have ef188 : x ◇ (x ◇ y) ≠ x ◇ (((y ◇ y) ◇ (x ◇ y)) ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef180 | exact superpose ef180 ef12
  have ef196 : x ◇ (x ◇ y) ≠ x ◇ (x ◇ (x ◇ ((y ◇ y) ◇ (x ◇ y)))) := by
    first | exact superpose ef12 ef188 | exact superpose ef188 ef12
  have ef204 : x ◇ (x ◇ y) ≠ x ◇ (x ◇ (x ◇ (y ◇ (x ◇ (y ◇ y))))) := by
    first | exact superpose ef12 ef196 | exact superpose ef196 ef12
  have ef210 : x ◇ (x ◇ y) ≠ x ◇ (x ◇ y) := by
    first | exact superpose ef10 ef204 | exact superpose ef204 ef10
  exact absurd rfl ef210

theorem Equation4435_termStructuralFrom_Equation546 :
    Law4435.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law4435.models_iff]
    exact fun x y ↦ @aux546_4435 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 4482 `x ◇ (y ◇ y) = (y ◇ y) ◇ x` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_4482 [Magma G] (h : Equation546 G) (x y : G) :
    (x ◇ x) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ x) = (((y ◇ y) ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ (y ◇ y))) ◇
      (x ◇ ((y ◇ y) ◇ (y ◇ y))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      (x ◇ x) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ x) ≠ (((y ◇ y) ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ (y ◇ y))) ◇
      (x ◇ ((y ◇ y) ◇ (y ◇ y))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef16 (X0 X1 X2 X3 : G) : X3 ◇ X2 = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1) := superpose ef8 ef8
  have ef25 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  have ef28 (X0 X1 X2 X3 : G) : X3 ◇ X2 = X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    first | exact superpose ef12 ef25 | exact superpose ef25 ef12
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef120 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X1 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X3) := superpose ef12 ef12
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef159 :
      (x ◇ x) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ x) ≠ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇
      (x ◇ (y ◇ (y ◇ (y ◇ y)))) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef164 :
      (x ◇ x) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ x) ≠ (y ◇ (y ◇ (y ◇ y))) ◇
      (x ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ y))))) := by
    first | exact superpose ef12 ef159 | exact superpose ef159 ef12
  have ef179 :
      (x ◇ x) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ x) ≠ (y ◇ (y ◇ (y ◇ y))) ◇
      (x ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (y ◇ (y ◇ y)))))) := by
    first | exact superpose ef120 ef164 | exact superpose ef164 ef120
  have ef187 :
      (x ◇ x) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ x) ≠ ((y ◇ y) ◇ x) ◇
      (((y ◇ y) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ (y ◇ (y ◇ (y ◇ y)))) := by
    first | exact superpose ef120 ef179 | exact superpose ef179 ef120
  have ef195 :
      (x ◇ x) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ x) ≠ ((y ◇ y) ◇ x) ◇
      ((y ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (y ◇ (y ◇ y)))))) := by
    first | exact superpose ef120 ef187 | exact superpose ef187 ef120
  have ef203 : (x ◇ x) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ x) ≠ ((y ◇ y) ◇ x) ◇ (y ◇ y) := by
    first | exact superpose ef28 ef195 | exact superpose ef195 ef28
  have ef209 : (x ◇ x) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ x) ≠ y ◇ (y ◇ ((y ◇ y) ◇ x)) := by
    first | exact superpose ef12 ef203 | exact superpose ef203 ef12
  have ef215 : (x ◇ x) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ x) ≠ y ◇ (x ◇ y) := by
    first | exact superpose ef121 ef209 | exact superpose ef209 ef121
  have ef221 : y ◇ (x ◇ y) ≠ x ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef215 | exact superpose ef215 ef12
  subsumption ef221 ef83

theorem Equation4482_termStructuralFrom_Equation546 :
    Law4482.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law4482.models_iff]
    exact fun x y ↦ @aux546_4482 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 4531 `x ◇ (y ◇ z) = (y ◇ z) ◇ x` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_4531 [Magma G] (h : Equation546 G) (x y z : G) :
    (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) = (((y ◇ y) ◇ (z ◇ y)) ◇ ((y ◇ y) ◇ (z ◇ y))) ◇
      (x ◇ ((y ◇ y) ◇ (z ◇ y))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ (((y ◇ y) ◇ (z ◇ y)) ◇ ((y ◇ y) ◇ (z ◇ y))) ◇
      (x ◇ ((y ◇ y) ◇ (z ◇ y))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X1 := by
    first | exact superpose ef5 ef9 | exact superpose ef9 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef23 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X0)) = X3 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef24 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X0)))) = X3 := by
    first | exact superpose ef12 ef23 | exact superpose ef23 ef12
  have ef83 (X0 X1 X2 X3 X4 : G) : X4 ◇ (X0 ◇ X3) = X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X4))) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef10 | exact superpose ef10 ef7
  have ef120 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X1 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X3) := superpose ef12 ef12
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef159 :
      (x ◇ x) ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ x) ≠ ((y ◇ (z ◇ (y ◇ y))) ◇ (y ◇ (z ◇ (y ◇ y)))) ◇
      (x ◇ (y ◇ (z ◇ (y ◇ y)))) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef164 :
      (x ◇ x) ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ x) ≠ (y ◇ (z ◇ (y ◇ y))) ◇
      (x ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (y ◇ (z ◇ (y ◇ y))))) := by
    first | exact superpose ef12 ef159 | exact superpose ef159 ef12
  have ef179 :
      (x ◇ x) ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ x) ≠ (y ◇ (z ◇ (y ◇ y))) ◇
      (x ◇ ((z ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (z ◇ (y ◇ y)))))) := by
    first | exact superpose ef120 ef164 | exact superpose ef164 ef120
  have ef187 :
      (x ◇ x) ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ x) ≠ ((z ◇ y) ◇ x) ◇
      (((y ◇ y) ◇ (y ◇ (z ◇ (y ◇ y)))) ◇ (y ◇ (z ◇ (y ◇ y)))) := by
    first | exact superpose ef120 ef179 | exact superpose ef179 ef120
  have ef195 :
      (x ◇ x) ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ x) ≠ ((z ◇ y) ◇ x) ◇
      ((z ◇ y) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ (z ◇ (y ◇ y)))))) := by
    first | exact superpose ef120 ef187 | exact superpose ef187 ef120
  have ef203 : (x ◇ x) ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ x) ≠ ((z ◇ y) ◇ x) ◇ (y ◇ y) := by
    first | exact superpose ef24 ef195 | exact superpose ef195 ef24
  have ef209 : (x ◇ x) ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ x) ≠ y ◇ (y ◇ ((z ◇ y) ◇ x)) := by
    first | exact superpose ef12 ef203 | exact superpose ef203 ef12
  have ef215 : (x ◇ x) ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ x) ≠ y ◇ (x ◇ z) := by
    first | exact superpose ef121 ef209 | exact superpose ef209 ef121
  have ef221 : y ◇ (x ◇ z) ≠ x ◇ ((y ◇ (z ◇ (y ◇ y))) ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef215 | exact superpose ef215 ef12
  subsumption ef221 ef83

theorem Equation4531_termStructuralFrom_Equation546 :
    Law4531.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law4531.models_iff]
    exact fun x y z ↦ @aux546_4531 G M h x y z
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- Equation 4544 `x ◇ (y ◇ z) = (z ◇ y) ◇ x` holds of the term `x □ y := (x ◇ x) ◇ (y ◇ x)` over
any magma satisfying equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. -/
private theorem aux546_4544 [Magma G] (h : Equation546 G) (x y z : G) :
    (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) = (((z ◇ z) ◇ (y ◇ z)) ◇ ((z ◇ z) ◇ (y ◇ z))) ◇
      (x ◇ ((z ◇ z) ◇ (y ◇ z))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef6 :
      (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ (((z ◇ z) ◇ (y ◇ z)) ◇ ((z ◇ z) ◇ (y ◇ z))) ◇
      (x ◇ ((z ◇ z) ◇ (y ◇ z))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X3 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := superpose ef5 ef5
  have ef12 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef14 (X0 X1 X2 X3 : G) : X3 ◇ (X0 ◇ (X3 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X1) := by
    first | exact superpose ef5 ef8 | exact superpose ef8 ef5
  have ef20 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0 = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef23 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X0)) = X3 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef24 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X2 ◇ (X1 ◇ X0)))) = X3 := by
    first | exact superpose ef12 ef23 | exact superpose ef23 ef12
  have ef27 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X1 ◇ X0)) = X3 ◇ (X0 ◇ (X3 ◇ X2)) := by
    first | exact superpose ef12 ef14 | exact superpose ef14 ef12
  have ef120 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X1 ◇ X2)) = (X1 ◇ X0) ◇ (X2 ◇ X3) := superpose ef12 ef12
  have ef121 (X0 X1 X2 : G) : X2 ◇ X0 = X1 ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef158 :
      (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ ((z ◇ z) ◇ (y ◇ z)) ◇
      (x ◇ (((z ◇ z) ◇ (y ◇ z)) ◇ ((z ◇ z) ◇ (y ◇ z)))) := by
    first | exact superpose ef12 ef6 | exact superpose ef6 ef12
  have ef165 :
      (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ ((z ◇ z) ◇ (y ◇ z)) ◇
      (x ◇ ((y ◇ z) ◇ ((z ◇ z) ◇ ((z ◇ z) ◇ (y ◇ z))))) := by
    first | exact superpose ef12 ef158 | exact superpose ef158 ef12
  have ef180 :
      (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ ((y ◇ z) ◇ x) ◇
      (((z ◇ z) ◇ ((z ◇ z) ◇ (y ◇ z))) ◇ ((z ◇ z) ◇ (y ◇ z))) := by
    first | exact superpose ef120 ef165 | exact superpose ef165 ef120
  have ef188 :
      (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ ((y ◇ z) ◇ x) ◇
      ((y ◇ (z ◇ z)) ◇ (z ◇ ((z ◇ z) ◇ ((z ◇ z) ◇ (y ◇ z))))) := by
    first | exact superpose ef120 ef180 | exact superpose ef180 ef120
  have ef196 : (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ ((y ◇ z) ◇ x) ◇ (z ◇ z) := by
    first | exact superpose ef24 ef188 | exact superpose ef188 ef24
  have ef204 : (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ z ◇ (z ◇ ((y ◇ z) ◇ x)) := by
    first | exact superpose ef12 ef196 | exact superpose ef196 ef12
  have ef210 : (x ◇ x) ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ x) ≠ z ◇ (x ◇ y) := by
    first | exact superpose ef121 ef204 | exact superpose ef204 ef121
  have ef216 : z ◇ (x ◇ y) ≠ x ◇ (((y ◇ y) ◇ (z ◇ y)) ◇ (x ◇ x)) := by
    first | exact superpose ef12 ef210 | exact superpose ef210 ef12
  have ef222 : z ◇ (x ◇ y) ≠ x ◇ (x ◇ (x ◇ ((y ◇ y) ◇ (z ◇ y)))) := by
    first | exact superpose ef12 ef216 | exact superpose ef216 ef12
  have ef228 : z ◇ (x ◇ y) ≠ x ◇ (x ◇ (x ◇ (y ◇ (z ◇ (y ◇ y))))) := by
    first | exact superpose ef12 ef222 | exact superpose ef222 ef12
  have ef246 (X0 X1 X2 X3 : G) : X3 ◇ (X0 ◇ X1) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2 := by
    first | exact superpose ef7 ef20 | exact superpose ef20 ef7
  have ef247 (X0 X1 X2 X3 : G) : (X1 ◇ X0) ◇ X2 = X3 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1))) := by
    first | exact superpose ef5 ef20 | exact superpose ef20 ef5
  have ef1085 (X0 : G) : z ◇ (x ◇ y) ≠ x ◇ (x ◇ (x ◇ (X0 ◇ (y ◇ (X0 ◇ z))))) := by
    first | exact superpose ef27 ef228 | exact superpose ef228 ef27
  have ef1086 (X0 : G) : z ◇ (x ◇ y) ≠ ((y ◇ (X0 ◇ z)) ◇ x) ◇ X0 := by
    first | exact superpose ef247 ef1085 | exact superpose ef1085 ef247
  subsumption ef1086 ef246

theorem Equation4544_termStructuralFrom_Equation546 :
    Law4544.TermStructuralFrom Law546 := by
  intro G M hGL
  have h : Equation546 G := Law546.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) (M.op y x))⟩, ?_, ?_, ?_⟩
  · rw [@Law4544.models_iff]
    exact fun x y z ↦ @aux546_4544 G M h x y z
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv546_dba7a67e G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := ((x ◇ y) ◇ y) ◇ y` of equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))` can
be undone: the operation is recovered as `x ◇ y = (x ◇ x) ◇ (y ◇ x)` read in `□`. -/
private theorem inv556_46197021 [Magma G] (h : Equation556 G) (x y : G) :
    (((((x ◇ x) ◇ x) ◇ x) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x) = x ◇
      y := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      (((((x ◇ x) ◇ x) ◇ x) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      (((y ◇ x) ◇ x) ◇ x) ≠ x ◇ y := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef21 :
      x ◇ y ≠ (((x ◇ ((x ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      (((y ◇ x) ◇ x) ◇ x) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef34 :
      x ◇ y ≠ (((y ◇ x) ◇ x) ◇ x) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef9 ef21 | exact superpose ef21 ef9
  have ef48 :
      x ◇ y ≠ (((y ◇ x) ◇ x) ◇ x) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef9 ef34 | exact superpose ef34 ef9
  have ef62 :
      x ◇ y ≠ (x ◇ ((y ◇ x) ◇ x)) ◇
      ((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x)))) := by
    first | exact superpose ef9 ef48 | exact superpose ef48 ef9
  have ef76 :
      x ◇ y ≠ (x ◇ (x ◇ (y ◇ x))) ◇
      ((x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ (y ◇ x))))) := by
    first | exact superpose ef9 ef62 | exact superpose ef62 ef9
  have ef90 :
      x ◇ y ≠ (x ◇ (x ◇ (y ◇ x))) ◇
      ((x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) := by
    first | exact superpose ef9 ef76 | exact superpose ef76 ef9
  have ef104 :
      x ◇ y ≠ (x ◇ (x ◇ (y ◇ x))) ◇
      ((x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (x ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef9 ef90 | exact superpose ef90 ef9
  have ef118 :
      x ◇ y ≠ (x ◇ (x ◇ (y ◇ x))) ◇
      ((x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ x))))) := by
    first | exact superpose ef9 ef104 | exact superpose ef104 ef9
  have ef132 :
      x ◇ y ≠ (x ◇ (x ◇ (x ◇ y))) ◇
      ((x ◇ (x ◇ (x ◇ y))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ y))))) := by
    first | exact superpose ef9 ef118 | exact superpose ef118 ef9
  have ef161 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef167 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X1 := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef506 (X0 : G) :
      x ◇ y ≠ (x ◇ (x ◇ (x ◇ y))) ◇
      ((x ◇ (x ◇ (x ◇ y))) ◇ ((X0 ◇ (x ◇ (X0 ◇ x))) ◇ (x ◇ (x ◇ (x ◇ y))))) := by
    first | exact superpose ef161 ef132 | exact superpose ef132 ef161
  have ef512 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ X4) = X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) := by
    first | exact superpose ef161 ef167 | exact superpose ef167 ef161
  have ef546 : x ◇ y ≠ x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))) := by
    first | exact superpose ef512 ef506 | exact superpose ef506 ef512
  subsumption ef546 ef10

/-- Equation 8 `x = x ◇ (x ◇ x)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over any magma
satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_8 [Magma G] (h : Equation556 G) (x : G) :
    x = ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef19 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef21 : x ≠ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef23 : x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) := by
    first | exact superpose ef9 ef21 | exact superpose ef21 ef9
  have ef31 : x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) := by
    first | exact superpose ef9 ef23 | exact superpose ef23 ef9
  have ef39 : x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x) := by
    first | exact superpose ef19 ef31 | exact superpose ef31 ef19
  have ef47 : x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))) := by
    first | exact superpose ef9 ef39 | exact superpose ef39 ef9
  have ef55 : x ≠ (x ◇ ((x ◇ x) ◇ x)) ◇ x := by
    first | exact superpose ef19 ef47 | exact superpose ef47 ef19
  have ef63 : x ≠ x ◇ (x ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef9 ef55 | exact superpose ef55 ef9
  subsumption ef63 ef19

theorem Equation8_termStructuralFrom_Equation556 :
    Law8.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law8.models_iff]
    exact fun x ↦ @aux556_8 G M h x
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 16 `x = y ◇ (y ◇ x)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over any magma
satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_16 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef20 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef69 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef113 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef20 ef20
  have ef130 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef20 ef10 | exact superpose ef10 ef20
  have ef155 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef69 ef69
  have ef188 : x ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x)) := by
    first | exact superpose ef69 ef6 | exact superpose ef6 ef69
  have ef200 : x ≠ (((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef130 ef188 | exact superpose ef188 ef130
  have ef207 : x ≠ (((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (((y ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef155 ef200 | exact superpose ef200 ef155
  subsumption ef207 ef113

theorem Equation16_termStructuralFrom_Equation556 :
    Law16.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law16.models_iff]
    exact fun x y ↦ @aux556_16 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 419 `x = x ◇ (x ◇ (y ◇ (y ◇ x)))` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_419 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((x ◇ (((x ◇ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (((y ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ (((x ◇ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (((y ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef23 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef181 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef190 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef23 ef23
  have ef203 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef23 ef10 | exact superpose ef10 ef23
  have ef267 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef181 ef181
  have ef313 :
      x ≠ ((x ◇ (((x ◇ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((y ◇ x) ◇ x) ◇
      x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef181 ef6 | exact superpose ef6 ef181
  have ef330 :
      x ≠ ((x ◇ (((x ◇ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ ((((y ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((x ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((y ◇ x) ◇ x) ◇
      x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef181 ef313 | exact superpose ef313 ef181
  have ef350 :
      x ≠ (((x ◇ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((x ◇
      (((x ◇ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) := by
    first | exact superpose ef203 ef330 | exact superpose ef330 ef203
  have ef368 :
      x ≠ (((x ◇ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((x ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))))) ◇ (x ◇
      (((x ◇ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef267 ef350 | exact superpose ef350 ef267
  have ef386 : x ≠ (((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef190 ef368 | exact superpose ef368 ef190
  have ef404 : x ≠ (((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (((y ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef267 ef386 | exact superpose ef386 ef267
  subsumption ef404 ef190

theorem Equation419_termStructuralFrom_Equation556 :
    Law419.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law419.models_iff]
    exact fun x y ↦ @aux556_419 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 436 `x = x ◇ (y ◇ (y ◇ (x ◇ x)))` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_436 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((x ◇ (((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((y ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ (((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((y ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef22 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef147 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef154 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X1)) = X3 := by
    first | exact superpose ef5 ef22 | exact superpose ef22 ef5
  have ef156 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef22 ef22
  have ef169 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef22 ef10 | exact superpose ef10 ef22
  have ef233 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef147 ef147
  have ef286 :
      x ≠ ((x ◇ ((((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      ((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))))) ◇ (((y ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((y ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef147 ef6 | exact superpose ef6 ef147
  have ef291 :
      x ≠ ((x ◇ ((((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      ((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))))) ◇ (((y ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ ((((y ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ ((y ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) := by
    first | exact superpose ef147 ef286 | exact superpose ef286 ef147
  have ef311 :
      x ≠ (((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((y ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ ((x ◇
      ((((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      ((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))))) ◇ (((y ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) := by
    first | exact superpose ef169 ef291 | exact superpose ef291 ef169
  have ef329 :
      x ≠ (((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((y ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ ((y ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (x ◇
      ((((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      ((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))))) := by
    first | exact superpose ef233 ef311 | exact superpose ef311 ef233
  have ef347 :
      x ≠ (((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((y ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (y ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))))) ◇ (x ◇
      ((((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))))))) := by
    first | exact superpose ef233 ef329 | exact superpose ef329 ef233
  have ef365 :
      x ≠ (((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ x) ◇
      x) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef156 ef347 | exact superpose ef347 ef156
  have ef383 :
      x ≠ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef169 ef365 | exact superpose ef365 ef169
  have ef401 :
      x ≠ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ x) ◇
      ((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      ((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) := by
    first | exact superpose ef233 ef383 | exact superpose ef383 ef233
  have ef419 :
      x ≠ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ x) ◇
      ((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef233 ef401 | exact superpose ef401 ef233
  have ef437 :
      x ≠ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ x) ◇
      ((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (y ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))))) := by
    first | exact superpose ef233 ef419 | exact superpose ef419 ef233
  have ef455 :
      x ≠ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ x) ◇
      ((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (y ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ (((x ◇ x) ◇ x) ◇ x))))))) := by
    first | exact superpose ef233 ef437 | exact superpose ef437 ef233
  have ef473 :
      x ≠ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ x) ◇
      ((y ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (y ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ (x ◇ ((x ◇ x) ◇ x)))))))) := by
    first | exact superpose ef147 ef455 | exact superpose ef455 ef147
  have ef491 :
      x ≠ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ x) ◇
      ((y ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ x))))))))) := by
    first | exact superpose ef147 ef473 | exact superpose ef473 ef147
  have ef509 :
      x ≠ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ x) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ x))))))))) := by
    first | exact superpose ef233 ef491 | exact superpose ef491 ef233
  have ef527 :
      x ≠ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((((x ◇ x) ◇ x) ◇ x) ◇
      ((x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ x))))))))) := by
    first | exact superpose ef147 ef509 | exact superpose ef509 ef147
  have ef545 :
      x ≠ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (((x ◇ ((x ◇ x) ◇ x)) ◇
      ((x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ x))))))))) := by
    first | exact superpose ef9 ef527 | exact superpose ef527 ef9
  have ef563 :
      x ≠ ((x ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (((x ◇ (x ◇ (x ◇ x))) ◇
      ((x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ x))))))))) := by
    first | exact superpose ef147 ef545 | exact superpose ef545 ef147
  have ef581 : x ≠ ((x ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef154 ef563 | exact superpose ef563 ef154
  have ef599 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ (x ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef169 ef581 | exact superpose ef581 ef169
  have ef617 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef233 ef599 | exact superpose ef599 ef233
  have ef635 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ x) := by
    first | exact superpose ef5 ef617 | exact superpose ef617 ef5
  have ef653 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef147 ef635 | exact superpose ef635 ef147
  have ef671 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef147 ef653 | exact superpose ef653 ef147
  have ef689 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ x := by
    first | exact superpose ef5 ef671 | exact superpose ef671 ef5
  have ef707 : x ≠ x ◇ ((x ◇ (x ◇ x)) ◇ x) := by
    first | exact superpose ef9 ef689 | exact superpose ef689 ef9
  have ef725 : x ≠ x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef147 ef707 | exact superpose ef707 ef147
  subsumption ef725 ef5

theorem Equation436_termStructuralFrom_Equation556 :
    Law436.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law436.models_iff]
    exact fun x y ↦ @aux556_436 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := ((y ◇ y) ◇ x) ◇ y` of equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))` can
be undone: the operation is recovered as `x ◇ y = x ◇ (x ◇ (x ◇ y))` read in `□`. -/
private theorem inv556_0b95aece [Magma G] (h : Equation556 G) (x y : G) :
    ((((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ≠ x ◇
      y := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef24 :
      x ◇ y ≠ (((((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇
      (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y))) ◇ x) ◇
      (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef27 :
      x ◇ y ≠ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇
      (((((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇
      (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y))) ◇ x) := by
    first | exact superpose ef9 ef24 | exact superpose ef24 ef9
  have ef39 :
      x ◇ y ≠ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (x ◇
      ((((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇
      (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)))) := by
    first | exact superpose ef9 ef27 | exact superpose ef27 ef9
  have ef51 :
      x ◇ y ≠ (((x ◇ (y ◇ y)) ◇ y) ◇ ((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x)) ◇ (x ◇
      ((((x ◇ (y ◇ y)) ◇ y) ◇ ((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x)) ◇
      (((x ◇ (y ◇ y)) ◇ y) ◇ ((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x)))) := by
    first | exact superpose ef9 ef39 | exact superpose ef39 ef9
  have ef63 :
      x ◇ y ≠ (((x ◇ (y ◇ y)) ◇ y) ◇ (x ◇ (((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)))) ◇ (x ◇
      ((((x ◇ (y ◇ y)) ◇ y) ◇ (x ◇ (((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)))) ◇
      (((x ◇ (y ◇ y)) ◇ y) ◇ (x ◇ (((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)))))) := by
    first | exact superpose ef9 ef51 | exact superpose ef51 ef9
  have ef75 :
      x ◇ y ≠ ((y ◇ (x ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))) ◇ (x ◇
      (((y ◇ (x ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))) ◇
      ((y ◇ (x ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))))) := by
    first | exact superpose ef9 ef63 | exact superpose ef63 ef9
  have ef87 :
      ((y ◇ (x ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))) ◇ (x ◇
      (((y ◇ (x ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))) ◇
      ((y ◇ (x ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))))) ≠ y ◇ x := by
    first | exact superpose ef9 ef75 | exact superpose ef75 ef9
  have ef99 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef499 (X0 : G) :
      y ◇ x ≠ ((X0 ◇ (x ◇ (X0 ◇ y))) ◇ (x ◇ ((X0 ◇ (x ◇ (X0 ◇ y))) ◇ (X0 ◇ (x ◇ (X0 ◇ y)))))) ◇ (x ◇
      (((X0 ◇ (x ◇ (X0 ◇ y))) ◇ (x ◇ ((X0 ◇ (x ◇ (X0 ◇ y))) ◇ (X0 ◇ (x ◇ (X0 ◇ y)))))) ◇
      ((X0 ◇ (x ◇ (X0 ◇ y))) ◇ (x ◇ ((X0 ◇ (x ◇ (X0 ◇ y))) ◇ (X0 ◇ (x ◇ (X0 ◇ y)))))))) := by
    first | exact superpose ef99 ef87 | exact superpose ef87 ef99
  have ef518 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    first | exact superpose ef99 ef10 | exact superpose ef10 ef99
  have ef528 (X0 : G) : y ◇ x ≠ x ◇ (x ◇ (X0 ◇ (x ◇ (X0 ◇ y)))) := by
    first | exact superpose ef518 ef499 | exact superpose ef499 ef518
  have ef545 : x ◇ y ≠ y ◇ x := by
    first | exact superpose ef10 ef528 | exact superpose ef528 ef10
  subsumption ef545 ef9

/-- Equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_464 [Magma G] (h : Equation556 G) (x y : G) :
    x = (((((((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇
      (((((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)))) ◇ y) ◇
      (((((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇
      (((((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)))) ◇ y) ◇
      (((((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef22 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef143 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef147 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef149 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X1 := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef169 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef22 ef10 | exact superpose ef10 ef22
  have ef199 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ (X3 ◇ ((X4 ◇ ((X0 ◇ X4) ◇ X1)) ◇ X2))) ◇ X0) = X3 := by
    first | exact superpose ef22 ef7 | exact superpose ef7 ef22
  have ef220 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ ((X0 ◇ X4) ◇ X1)) ◇ X2)))) = X3 := by
    first | exact superpose ef147 ef199 | exact superpose ef199 ef147
  have ef233 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef147 ef147
  have ef618 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) ◇ X3 := superpose ef169 ef169
  have ef633 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = (X1 ◇ X0) ◇ X2 := by
    first | exact superpose ef169 ef9 | exact superpose ef9 ef169
  have ef637 (X0 X1 X2 X3 : G) : X3 ◇ ((X0 ◇ X1) ◇ X2) = X3 ◇ ((X1 ◇ X0) ◇ X2) := by
    first | exact superpose ef169 ef147 | exact superpose ef147 ef169
  have ef670 (X0 X1 X2 X3 : G) : X3 ◇ (X0 ◇ (X2 ◇ X1)) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := by
    first | exact superpose ef169 ef147 | exact superpose ef147 ef169
  have ef1524 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) := by
    first | exact superpose ef143 ef149 | exact superpose ef149 ef143
  have ef1574 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) ◇ X3 = (X0 ◇ (X1 ◇ X2)) ◇ X3 := by
    first | exact superpose ef169 ef633 | exact superpose ef633 ef169
  have ef1637 :
      x ≠ (((((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)))) ◇ y) ◇
      (((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇ ((((y ◇
      ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) := by
    first | exact superpose ef633 ef6 | exact superpose ef6 ef633
  have ef1680 :
      x ≠ (((((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)))) ◇ y) ◇ (((((y ◇
      y) ◇ x) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x)) := by
    first | exact superpose ef233 ef1637 | exact superpose ef1637 ef233
  have ef1697 :
      x ≠ (((((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)))) ◇ y) ◇ (((((y ◇
      y) ◇ x) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) := by
    first | exact superpose ef670 ef1680 | exact superpose ef1680 ef670
  have ef1711 :
      x ≠ (((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x)) ◇
      (((((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)))) ◇ y) := by
    first | exact superpose ef618 ef1697 | exact superpose ef1697 ef618
  have ef1725 :
      x ≠ (((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x)) ◇ (y ◇
      ((((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) := by
    first | exact superpose ef147 ef1711 | exact superpose ef1711 ef147
  have ef1739 :
      x ≠ (((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) ◇ (y ◇
      ((((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) := by
    first | exact superpose ef1574 ef1725 | exact superpose ef1725 ef1574
  have ef1753 :
      x ≠ (((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x)) ◇
      (((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) := by
    first | exact superpose ef233 ef1739 | exact superpose ef1739 ef233
  have ef1767 :
      x ≠ (((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x)) ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x)))) := by
    first | exact superpose ef233 ef1753 | exact superpose ef1753 ef233
  have ef1781 :
      x ≠ (((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x)) ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))))) := by
    first | exact superpose ef670 ef1767 | exact superpose ef1767 ef670
  have ef1795 :
      x ≠ (((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ x)))) := by
    first | exact superpose ef670 ef1781 | exact superpose ef1781 ef670
  have ef1809 :
      x ≠ (((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))))) := by
    first | exact superpose ef670 ef1795 | exact superpose ef1795 ef670
  have ef1823 :
      x ≠ (((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))) ◇
      (((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇ (x ◇
      (((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))))))) := by
    first | exact superpose ef637 ef1809 | exact superpose ef1809 ef637
  have ef1837 :
      x ≠ x ◇ (y ◇ ((((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y))) := by
    first | exact superpose ef1524 ef1823 | exact superpose ef1823 ef1524
  have ef1851 :
      x ≠ x ◇ (y ◇ ((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x))) := by
    first | exact superpose ef670 ef1837 | exact superpose ef1837 ef670
  have ef1865 :
      x ≠ x ◇ (y ◇ ((((y ◇ y) ◇ x) ◇ y) ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y))))) := by
    first | exact superpose ef670 ef1851 | exact superpose ef1851 ef670
  subsumption ef1865 ef220

theorem Equation464_termStructuralFrom_Equation556 :
    Law464.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law464.models_iff]
    exact fun x y ↦ @aux556_464 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 466 `x = y ◇ (x ◇ (x ◇ (y ◇ x)))` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_466 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((y ◇ (((x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (((x ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((y ◇ (((x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (((x ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef23 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef217 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef226 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef23 ef23
  have ef239 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef23 ef10 | exact superpose ef10 ef23
  have ef303 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef217 ef217
  have ef358 :
      x ≠ ((y ◇ ((((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      ((x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))))) ◇ (((x ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (((x ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef217 ef6 | exact superpose ef6 ef217
  have ef359 :
      x ≠ ((y ◇ ((((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      ((x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))))) ◇ (((x ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ ((((x ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((x ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) := by
    first | exact superpose ef217 ef358 | exact superpose ef358 ef217
  have ef379 :
      x ≠ (((x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (((x ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((y ◇
      ((((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      ((x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))))) ◇ (((x ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) := by
    first | exact superpose ef239 ef359 | exact superpose ef359 ef239
  have ef397 :
      x ≠ (((x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (((x ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ ((x ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇ (y ◇
      ((((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      ((x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))))) := by
    first | exact superpose ef303 ef379 | exact superpose ef379 ef303
  have ef415 :
      x ≠ (((x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (((x ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (x ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))))) ◇ (y ◇
      ((((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))))))) := by
    first | exact superpose ef303 ef397 | exact superpose ef397 ef303
  have ef433 :
      x ≠ (((x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ ((((y ◇ x) ◇ x) ◇
      x) ◇ (y ◇ (((y ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef226 ef415 | exact superpose ef415 ef226
  have ef451 :
      x ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef239 ef433 | exact superpose ef433 ef239
  have ef469 :
      x ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇
      ((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) := by
    first | exact superpose ef303 ef451 | exact superpose ef451 ef303
  have ef487 :
      x ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇
      ((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (x ◇ (((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef303 ef469 | exact superpose ef469 ef303
  have ef505 :
      x ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇
      ((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (x ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))))) := by
    first | exact superpose ef303 ef487 | exact superpose ef487 ef303
  have ef523 :
      x ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇
      ((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (x ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (x ◇ (((y ◇ x) ◇ x) ◇ x))))))) := by
    first | exact superpose ef303 ef505 | exact superpose ef505 ef303
  have ef541 :
      x ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇
      ((x ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (x ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((y ◇ x) ◇ x)))))))) := by
    first | exact superpose ef217 ef523 | exact superpose ef523 ef217
  have ef559 :
      x ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇
      (y ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (x ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ y))))) := by
    first | exact superpose ef23 ef541 | exact superpose ef541 ef23
  have ef577 :
      x ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇
      (y ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (x ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (x ◇ ((y ◇ x) ◇ x))))))) := by
    first | exact superpose ef217 ef559 | exact superpose ef559 ef217
  have ef595 :
      x ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇
      (y ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (x ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (y ◇ x)))))))) := by
    first | exact superpose ef217 ef577 | exact superpose ef577 ef217
  have ef613 :
      x ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇
      (y ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))))) := by
    first | exact superpose ef217 ef595 | exact superpose ef595 ef217
  have ef631 :
      x ≠ ((y ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇
      (y ◇ (x ◇ ((y ◇ x) ◇ x)))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (x ◇ ((y ◇ x) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))))) := by
    first | exact superpose ef217 ef613 | exact superpose ef613 ef217
  have ef649 :
      x ≠ ((y ◇ (x ◇ (x ◇ (y ◇ x)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇
      (y ◇ (x ◇ (x ◇ (y ◇ x))))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (y ◇ x))))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))))) := by
    first | exact superpose ef217 ef631 | exact superpose ef631 ef217
  have ef667 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇
      (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))))) := by
    first | exact superpose ef217 ef649 | exact superpose ef649 ef217
  have ef685 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇
      (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))))) := by
    first | exact superpose ef9 ef667 | exact superpose ef667 ef9
  have ef703 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (y ◇ x)))) ◇ (((x ◇ (x ◇ (y ◇ x))) ◇
      (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇ (((x ◇ (x ◇ (y ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))))) := by
    first | exact superpose ef217 ef685 | exact superpose ef685 ef217
  have ef721 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (((x ◇ (x ◇ (x ◇ y))) ◇
      (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇ (((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))))) := by
    first | exact superpose ef217 ef703 | exact superpose ef703 ef217
  have ef739 :
      x ≠ (((x ◇ (x ◇ y)) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇ (((x ◇ (x ◇ (x ◇ y))) ◇
      (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇ (((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))))) := by
    first | exact superpose ef239 ef721 | exact superpose ef721 ef239
  have ef757 :
      x ≠ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇ (((x ◇ (x ◇ (x ◇ y))) ◇
      (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇ (((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))) ◇
      (x ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))))) := by
    first | exact superpose ef9 ef739 | exact superpose ef739 ef9
  subsumption ef757 ef5

theorem Equation466_termStructuralFrom_Equation556 :
    Law466.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law466.models_iff]
    exact fun x y ↦ @aux556_466 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 500 `x = y ◇ (y ◇ (x ◇ (x ◇ x)))` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_500 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((y ◇ (((y ◇ (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((x ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((y ◇ (((y ◇ (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((x ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef22 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef229 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef273 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef22 ef22
  have ef290 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef22 ef10 | exact superpose ef10 ef22
  have ef315 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef229 ef229
  have ef361 :
      x ≠ ((y ◇ (((y ◇ (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef229 ef6 | exact superpose ef6 ef229
  have ef378 :
      x ≠ ((y ◇ (((y ◇ (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ ((((x ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ ((y ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ ((((x ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef229 ef361 | exact superpose ef361 ef229
  have ef398 :
      x ≠ (((y ◇ (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ ((y ◇
      (((y ◇ (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((y ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) := by
    first | exact superpose ef290 ef378 | exact superpose ef378 ef290
  have ef416 :
      x ≠ (((y ◇ (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ (((x ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ ((y ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))))) ◇ (y ◇
      (((y ◇ (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef315 ef398 | exact superpose ef398 ef315
  have ef434 : x ≠ (((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef273 ef416 | exact superpose ef416 ef273
  have ef452 : x ≠ (((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef315 ef434 | exact superpose ef434 ef315
  subsumption ef452 ef273

theorem Equation500_termStructuralFrom_Equation556 :
    Law500.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law500.models_iff]
    exact fun x y ↦ @aux556_500 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 504 `x = y ◇ (y ◇ (x ◇ (y ◇ y)))` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_504 [Magma G] (h : Equation556 G) (x y : G) :
    x = (((((((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)))) ◇ y) ◇
      (((((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)))) ◇ y) ◇
      (((((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef22 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef143 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef147 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef149 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X1 := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef169 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef22 ef10 | exact superpose ef10 ef22
  have ef199 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ (X3 ◇ ((X4 ◇ ((X0 ◇ X4) ◇ X1)) ◇ X2))) ◇ X0) = X3 := by
    first | exact superpose ef22 ef7 | exact superpose ef7 ef22
  have ef220 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ ((X0 ◇ X4) ◇ X1)) ◇ X2)))) = X3 := by
    first | exact superpose ef147 ef199 | exact superpose ef199 ef147
  have ef233 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef147 ef147
  have ef618 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) ◇ X3 := superpose ef169 ef169
  have ef633 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = (X1 ◇ X0) ◇ X2 := by
    first | exact superpose ef169 ef9 | exact superpose ef9 ef169
  have ef637 (X0 X1 X2 X3 : G) : X3 ◇ ((X0 ◇ X1) ◇ X2) = X3 ◇ ((X1 ◇ X0) ◇ X2) := by
    first | exact superpose ef169 ef147 | exact superpose ef147 ef169
  have ef670 (X0 X1 X2 X3 : G) : X3 ◇ (X0 ◇ (X2 ◇ X1)) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := by
    first | exact superpose ef169 ef147 | exact superpose ef147 ef169
  have ef1524 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) := by
    first | exact superpose ef143 ef149 | exact superpose ef149 ef143
  have ef1574 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) ◇ X3 = (X0 ◇ (X1 ◇ X2)) ◇ X3 := by
    first | exact superpose ef169 ef633 | exact superpose ef633 ef169
  have ef1637 :
      x ≠ (((((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)))) ◇ y) ◇
      (((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇ ((((y ◇
      ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef633 ef6 | exact superpose ef6 ef633
  have ef1680 :
      x ≠ (((((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)))) ◇ y) ◇ (((((y ◇
      y) ◇ y) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y)) := by
    first | exact superpose ef233 ef1637 | exact superpose ef1637 ef233
  have ef1697 :
      x ≠ (((((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)))) ◇ y) ◇ (((((y ◇
      y) ◇ y) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) := by
    first | exact superpose ef670 ef1680 | exact superpose ef1680 ef670
  have ef1711 :
      x ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y)) ◇
      (((((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)))) ◇ y) := by
    first | exact superpose ef618 ef1697 | exact superpose ef1697 ef618
  have ef1725 :
      x ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y)) ◇ (y ◇
      ((((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) := by
    first | exact superpose ef147 ef1711 | exact superpose ef1711 ef147
  have ef1739 :
      x ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ (y ◇
      ((((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) := by
    first | exact superpose ef1574 ef1725 | exact superpose ef1725 ef1574
  have ef1753 :
      x ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y)) ◇
      (((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) := by
    first | exact superpose ef233 ef1739 | exact superpose ef1739 ef233
  have ef1767 :
      x ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y)) ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y)))) := by
    first | exact superpose ef233 ef1753 | exact superpose ef1753 ef233
  have ef1781 :
      x ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y)) ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))))) := by
    first | exact superpose ef670 ef1767 | exact superpose ef1767 ef670
  have ef1795 :
      x ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y)))) := by
    first | exact superpose ef670 ef1781 | exact superpose ef1781 ef670
  have ef1809 :
      x ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))))) := by
    first | exact superpose ef670 ef1795 | exact superpose ef1795 ef670
  have ef1823 :
      x ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇ (y ◇
      (((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))))))) := by
    first | exact superpose ef637 ef1809 | exact superpose ef1809 ef637
  have ef1837 :
      x ≠ y ◇ (y ◇ ((((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef1524 ef1823 | exact superpose ef1823 ef1524
  have ef1851 :
      x ≠ y ◇ (y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x))) := by
    first | exact superpose ef670 ef1837 | exact superpose ef1837 ef670
  have ef1865 :
      x ≠ y ◇ (y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))))) := by
    first | exact superpose ef670 ef1851 | exact superpose ef1851 ef670
  subsumption ef1865 ef220

theorem Equation504_termStructuralFrom_Equation556 :
    Law504.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law504.models_iff]
    exact fun x y ↦ @aux556_504 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_546 [Magma G] (h : Equation556 G) (x y z : G) :
    x = (((((((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇
      (((((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)))) ◇ y) ◇
      (((((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇
      (((((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)))) ◇ y) ◇
      (((((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef22 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef143 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef147 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef149 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X1 := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef169 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef22 ef10 | exact superpose ef10 ef22
  have ef199 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ (X3 ◇ ((X4 ◇ ((X0 ◇ X4) ◇ X1)) ◇ X2))) ◇ X0) = X3 := by
    first | exact superpose ef22 ef7 | exact superpose ef7 ef22
  have ef220 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ ((X0 ◇ X4) ◇ X1)) ◇ X2)))) = X3 := by
    first | exact superpose ef147 ef199 | exact superpose ef199 ef147
  have ef233 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef147 ef147
  have ef618 (X0 X1 X2 X3 : G) :
      X3 ◇ (X0 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) ◇ X3 := superpose ef169 ef169
  have ef633 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = (X1 ◇ X0) ◇ X2 := by
    first | exact superpose ef169 ef9 | exact superpose ef9 ef169
  have ef637 (X0 X1 X2 X3 : G) : X3 ◇ ((X0 ◇ X1) ◇ X2) = X3 ◇ ((X1 ◇ X0) ◇ X2) := by
    first | exact superpose ef169 ef147 | exact superpose ef147 ef169
  have ef670 (X0 X1 X2 X3 : G) : X3 ◇ (X0 ◇ (X2 ◇ X1)) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := by
    first | exact superpose ef169 ef147 | exact superpose ef147 ef169
  have ef1524 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) := by
    first | exact superpose ef143 ef149 | exact superpose ef149 ef143
  have ef1574 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) ◇ X3 = (X0 ◇ (X1 ◇ X2)) ◇ X3 := by
    first | exact superpose ef169 ef633 | exact superpose ef633 ef169
  have ef1637 :
      x ≠ (((((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)))) ◇ y) ◇
      (((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇ ((((y ◇
      ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) := by
    first | exact superpose ef633 ef6 | exact superpose ef6 ef633
  have ef1680 :
      x ≠ (((((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)))) ◇ y) ◇ (((((y ◇
      y) ◇ z) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x)) ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z)) := by
    first | exact superpose ef233 ef1637 | exact superpose ef1637 ef233
  have ef1697 :
      x ≠ (((((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)))) ◇ y) ◇ (((((y ◇
      y) ◇ z) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) := by
    first | exact superpose ef670 ef1680 | exact superpose ef1680 ef670
  have ef1711 :
      x ≠ (((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x)) ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z)) ◇
      (((((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)))) ◇ y) := by
    first | exact superpose ef618 ef1697 | exact superpose ef1697 ef618
  have ef1725 :
      x ≠ (((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x)) ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z)) ◇ (y ◇
      ((((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) := by
    first | exact superpose ef147 ef1711 | exact superpose ef1711 ef147
  have ef1739 :
      x ≠ (((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) ◇ (y ◇
      ((((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇
      (((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) := by
    first | exact superpose ef1574 ef1725 | exact superpose ef1725 ef1574
  have ef1753 :
      x ≠ (((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z)) ◇
      (((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) := by
    first | exact superpose ef233 ef1739 | exact superpose ef1739 ef233
  have ef1767 :
      x ≠ (((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z)) ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z)))) := by
    first | exact superpose ef233 ef1753 | exact superpose ef1753 ef233
  have ef1781 :
      x ≠ (((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z)) ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))))) := by
    first | exact superpose ef670 ef1767 | exact superpose ef1767 ef670
  have ef1795 :
      x ≠ (((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) ◇ z)))) := by
    first | exact superpose ef670 ef1781 | exact superpose ef1781 ef670
  have ef1809 :
      x ≠ (((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))))) := by
    first | exact superpose ef670 ef1795 | exact superpose ef1795 ef670
  have ef1823 :
      x ≠ (((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) ◇ (y ◇
      ((((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))) ◇
      (((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x)) ◇ (z ◇
      (((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇
      ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))))))) := by
    first | exact superpose ef637 ef1809 | exact superpose ef1809 ef637
  have ef1837 :
      x ≠ z ◇ (y ◇ ((((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ z) ◇ y))) := by
    first | exact superpose ef1524 ef1823 | exact superpose ef1823 ef1524
  have ef1851 :
      x ≠ z ◇ (y ◇ ((((y ◇ y) ◇ z) ◇ y) ◇ (((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y)) ◇ x))) := by
    first | exact superpose ef670 ef1837 | exact superpose ef1837 ef670
  have ef1865 :
      x ≠ z ◇ (y ◇ ((((y ◇ y) ◇ z) ◇ y) ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ z)) ◇ (((y ◇ y) ◇ z) ◇ y))))) := by
    first | exact superpose ef670 ef1851 | exact superpose ef1851 ef670
  subsumption ef1865 ef220

theorem Equation546_termStructuralFrom_Equation556 :
    Law546.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law546.models_iff]
    exact fun x y z ↦ @aux556_546 G M h x y z
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 817 `x = x ◇ ((x ◇ x) ◇ (x ◇ x))` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_817 [Magma G] (h : Equation556 G) (x : G) :
    x = ((((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ x) ◇ x))) ◇ x) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇
      x)) ◇ (((x ◇ x) ◇ x) ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ x) ◇ x))) ◇ x) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇
      x)) ◇ (((x ◇ x) ◇ x) ◇ x)) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef24 :
      x ≠ (((((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ (x ◇ x)) ◇ x))) ◇ x) ◇ (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇
      x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef26 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef27 :
      x ≠ (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇
      x)) ◇ (((((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ (x ◇ x)) ◇ x))) ◇ x) := by
    first | exact superpose ef9 ef24 | exact superpose ef24 ef9
  have ef39 :
      x ≠ (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇
      x)) ◇ (x ◇ ((((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ (x ◇ x)) ◇ x)))) := by
    first | exact superpose ef9 ef27 | exact superpose ef27 ef9
  have ef51 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇
      x))) ◇ (x ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef9 ef39 | exact superpose ef39 ef9
  have ef63 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇
      ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇
      (((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇
      (((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)))))) := by
    first | exact superpose ef9 ef51 | exact superpose ef51 ef9
  have ef75 :
      x ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇
      (x ◇ (x ◇ (x ◇ x)))))) ◇ (x ◇ (((x ◇ (x ◇ (x ◇ x))) ◇
      ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇
      ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef9 ef63 | exact superpose ef63 ef9
  have ef87 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef487 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := by
    first | exact superpose ef87 ef26 | exact superpose ef26 ef87
  have ef511 (X0 : G) :
      x ≠ (X0 ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ X0))) ◇ (x ◇
      ((X0 ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ X0))) ◇
      (X0 ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ X0))))) := by
    first | exact superpose ef87 ef75 | exact superpose ef75 ef87
  have ef533 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    first | exact superpose ef87 ef10 | exact superpose ef10 ef87
  have ef539 : x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef533 ef511 | exact superpose ef511 ef533
  subsumption ef539 ef487

theorem Equation817_termStructuralFrom_Equation556 :
    Law817.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law817.models_iff]
    exact fun x ↦ @aux556_817 G M h x
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 833 `x = x ◇ ((y ◇ x) ◇ (x ◇ y))` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_833 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      (((y ◇ y) ◇ x) ◇ y)) ◇ ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇ ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇
      x)) ◇ (((y ◇ y) ◇ x) ◇ y)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      (((y ◇ y) ◇ x) ◇ y)) ◇ ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      (((y ◇ y) ◇ x) ◇ y))) ◇ x) ◇ ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇
      x)) ◇ (((y ◇ y) ◇ x) ◇ y)) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef22 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef30 :
      x ≠ (((((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      ((x ◇ (y ◇ y)) ◇ y)) ◇ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      ((x ◇ (y ◇ y)) ◇ y))) ◇ x) ◇ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇
      x)) ◇ ((x ◇ (y ◇ y)) ◇ y)) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef31 :
      x ≠ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ ((x ◇ (y ◇ y)) ◇
      y)) ◇ (((((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      ((x ◇ (y ◇ y)) ◇ y)) ◇ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      ((x ◇ (y ◇ y)) ◇ y))) ◇ x) := by
    first | exact superpose ef9 ef30 | exact superpose ef30 ef9
  have ef47 :
      x ≠ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ ((x ◇ (y ◇ y)) ◇
      y)) ◇ (x ◇ ((((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      ((x ◇ (y ◇ y)) ◇ y)) ◇ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      ((x ◇ (y ◇ y)) ◇ y)))) := by
    first | exact superpose ef9 ef31 | exact superpose ef31 ef9
  have ef63 :
      x ≠ (((x ◇ (y ◇ y)) ◇ y) ◇ ((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇
      x))) ◇ (x ◇ ((((x ◇ (y ◇ y)) ◇ y) ◇
      ((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x))) ◇ (((x ◇ (y ◇ y)) ◇ y) ◇
      ((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x))))) := by
    first | exact superpose ef9 ef47 | exact superpose ef47 ef9
  have ef79 :
      x ≠ (((x ◇ (y ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ x) ◇ (((x ◇ (y ◇ y)) ◇ y) ◇
      ((x ◇ (y ◇ y)) ◇ y)))) ◇ (x ◇ ((((x ◇ (y ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ x) ◇ (((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)))) ◇ (((x ◇ (y ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ x) ◇ (((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)))))) := by
    first | exact superpose ef9 ef63 | exact superpose ef63 ef9
  have ef95 :
      x ≠ ((y ◇ (x ◇ (y ◇ y))) ◇ ((((x ◇ x) ◇ y) ◇ x) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇
      (y ◇ (x ◇ (y ◇ y)))))) ◇ (x ◇ (((y ◇ (x ◇ (y ◇ y))) ◇
      ((((x ◇ x) ◇ y) ◇ x) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇
      ((((x ◇ x) ◇ y) ◇ x) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))))) := by
    first | exact superpose ef9 ef79 | exact superpose ef79 ef9
  have ef111 :
      x ≠ ((y ◇ (x ◇ (y ◇ y))) ◇ ((x ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇
      (y ◇ (x ◇ (y ◇ y)))))) ◇ (x ◇ (((y ◇ (x ◇ (y ◇ y))) ◇
      ((x ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇
      ((x ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))))) := by
    first | exact superpose ef9 ef95 | exact superpose ef95 ef9
  have ef127 :
      x ≠ ((y ◇ (x ◇ (y ◇ y))) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇
      (y ◇ (x ◇ (y ◇ y)))))) ◇ (x ◇ (((y ◇ (x ◇ (y ◇ y))) ◇
      ((x ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇
      ((x ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))))) := by
    first | exact superpose ef9 ef111 | exact superpose ef111 ef9
  have ef143 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef584 (X0 X1 X2 X3 X4 : G) :
      (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := by
    first | exact superpose ef143 ef22 | exact superpose ef22 ef143
  have ef588 (X0 : G) :
      x ≠ ((X0 ◇ (x ◇ (X0 ◇ y))) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ ((X0 ◇ (x ◇ (X0 ◇ y))) ◇
      (X0 ◇ (x ◇ (X0 ◇ y)))))) ◇ (x ◇ (((X0 ◇ (x ◇ (X0 ◇ y))) ◇
      ((x ◇ (y ◇ (x ◇ x))) ◇ ((X0 ◇ (x ◇ (X0 ◇ y))) ◇ (X0 ◇ (x ◇ (X0 ◇ y)))))) ◇
      ((X0 ◇ (x ◇ (X0 ◇ y))) ◇
      ((x ◇ (y ◇ (x ◇ x))) ◇ ((X0 ◇ (x ◇ (X0 ◇ y))) ◇ (X0 ◇ (x ◇ (X0 ◇ y)))))))) := by
    first | exact superpose ef143 ef127 | exact superpose ef127 ef143
  have ef607 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    first | exact superpose ef143 ef10 | exact superpose ef10 ef143
  have ef618 (X0 : G) : x ≠ (x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (X0 ◇ (x ◇ (X0 ◇ y)))) := by
    first | exact superpose ef607 ef588 | exact superpose ef588 ef607
  subsumption ef618 ef584

theorem Equation833_termStructuralFrom_Equation556 :
    Law833.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law833.models_iff]
    exact fun x y ↦ @aux556_833 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 872 `x = y ◇ ((x ◇ x) ◇ (y ◇ x))` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_872 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((((((((x ◇ x) ◇ y) ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ y) ◇ x)) ◇ ((((((x ◇ x) ◇ y) ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ y) ◇ x))) ◇ y) ◇ ((((((x ◇ x) ◇ y) ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇
      x)) ◇ (((x ◇ x) ◇ y) ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((((((((x ◇ x) ◇ y) ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ y) ◇ x)) ◇ ((((((x ◇ x) ◇ y) ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ y) ◇ x))) ◇ y) ◇ ((((((x ◇ x) ◇ y) ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇
      x)) ◇ (((x ◇ x) ◇ y) ◇ x)) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef28 :
      x ≠ (((((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ x))) ◇ y) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇
      x)) ◇ ((y ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef31 :
      x ≠ (((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇
      x)) ◇ (((((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ x))) ◇ y) := by
    first | exact superpose ef9 ef28 | exact superpose ef28 ef9
  have ef47 :
      x ≠ (((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ ((y ◇ (x ◇ x)) ◇
      x)) ◇ (y ◇ ((((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ x)) ◇ (((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      ((y ◇ (x ◇ x)) ◇ x)))) := by
    first | exact superpose ef9 ef31 | exact superpose ef31 ef9
  have ef63 :
      x ≠ (((y ◇ (x ◇ x)) ◇ x) ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇
      x))) ◇ (y ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef9 ef47 | exact superpose ef47 ef9
  have ef79 :
      x ≠ (((y ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇
      ((y ◇ (x ◇ x)) ◇ x)))) ◇ (y ◇ ((((y ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)))) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)))))) := by
    first | exact superpose ef9 ef63 | exact superpose ef63 ef9
  have ef95 :
      x ≠ ((x ◇ (y ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇
      (x ◇ (y ◇ (x ◇ x)))))) ◇ (y ◇ (((x ◇ (y ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (y ◇ (x ◇ x)))))) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (y ◇ (x ◇ x)))))))) := by
    first | exact superpose ef9 ef79 | exact superpose ef79 ef9
  have ef111 :
      x ≠ ((x ◇ (y ◇ (x ◇ x))) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇
      (x ◇ (y ◇ (x ◇ x)))))) ◇ (y ◇ (((x ◇ (y ◇ (x ◇ x))) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (y ◇ (x ◇ x)))))) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (y ◇ (x ◇ x)))))))) := by
    first | exact superpose ef9 ef95 | exact superpose ef95 ef9
  have ef127 :
      x ≠ ((x ◇ (y ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇
      (x ◇ (y ◇ (x ◇ x)))))) ◇ (y ◇ (((x ◇ (y ◇ (x ◇ x))) ◇
      ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (y ◇ (x ◇ x)))))) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇
      ((x ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (y ◇ (x ◇ x)))))))) := by
    first | exact superpose ef9 ef111 | exact superpose ef111 ef9
  have ef143 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef588 (X0 : G) :
      x ≠ ((X0 ◇ (y ◇ (X0 ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ ((X0 ◇ (y ◇ (X0 ◇ x))) ◇
      (X0 ◇ (y ◇ (X0 ◇ x)))))) ◇ (y ◇ (((X0 ◇ (y ◇ (X0 ◇ x))) ◇
      ((x ◇ (x ◇ (x ◇ x))) ◇ ((X0 ◇ (y ◇ (X0 ◇ x))) ◇ (X0 ◇ (y ◇ (X0 ◇ x)))))) ◇
      ((X0 ◇ (y ◇ (X0 ◇ x))) ◇
      ((x ◇ (x ◇ (x ◇ x))) ◇ ((X0 ◇ (y ◇ (X0 ◇ x))) ◇ (X0 ◇ (y ◇ (X0 ◇ x)))))))) := by
    first | exact superpose ef143 ef127 | exact superpose ef127 ef143
  have ef607 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    first | exact superpose ef143 ef10 | exact superpose ef10 ef143
  have ef618 (X0 : G) : x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ (y ◇ (X0 ◇ (y ◇ (X0 ◇ x)))) := by
    first | exact superpose ef607 ef588 | exact superpose ef588 ef607
  have ef636 : x ≠ (x ◇ (x ◇ (x ◇ x))) ◇ x := by
    first | exact superpose ef10 ef618 | exact superpose ef618 ef10
  have ef641 : x ≠ x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef9 ef636 | exact superpose ef636 ef9
  subsumption ef641 ef5

theorem Equation872_termStructuralFrom_Equation556 :
    Law872.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law872.models_iff]
    exact fun x y ↦ @aux556_872 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 879 `x = y ◇ ((x ◇ y) ◇ (x ◇ x))` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_879 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      (((x ◇ x) ◇ x) ◇ x))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇
      y)) ◇ (((x ◇ x) ◇ x) ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      (((x ◇ x) ◇ x) ◇ x))) ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇
      y)) ◇ (((x ◇ x) ◇ x) ◇ x)) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef30 :
      x ≠ (((((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((x ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((x ◇ (x ◇ x)) ◇ x))) ◇ y) ◇ (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇
      y)) ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef31 :
      x ≠ (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ ((x ◇ (x ◇ x)) ◇
      x)) ◇ (((((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((x ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((x ◇ (x ◇ x)) ◇ x))) ◇ y) := by
    first | exact superpose ef9 ef30 | exact superpose ef30 ef9
  have ef47 :
      x ≠ (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ ((x ◇ (x ◇ x)) ◇
      x)) ◇ (y ◇ ((((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((x ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇
      ((x ◇ (x ◇ x)) ◇ x)))) := by
    first | exact superpose ef9 ef31 | exact superpose ef31 ef9
  have ef63 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇
      y))) ◇ (y ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((y ◇ y) ◇ x) ◇ y))))) := by
    first | exact superpose ef9 ef47 | exact superpose ef47 ef9
  have ef79 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ ((((y ◇ y) ◇ x) ◇ y) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇
      ((x ◇ (x ◇ x)) ◇ x)))) ◇ (y ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇
      ((((y ◇ y) ◇ x) ◇ y) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇
      ((((y ◇ y) ◇ x) ◇ y) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)))))) := by
    first | exact superpose ef9 ef63 | exact superpose ef63 ef9
  have ef95 :
      x ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ ((((y ◇ y) ◇ x) ◇ y) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇
      (x ◇ (x ◇ (x ◇ x)))))) ◇ (y ◇ (((x ◇ (x ◇ (x ◇ x))) ◇
      ((((y ◇ y) ◇ x) ◇ y) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇
      ((((y ◇ y) ◇ x) ◇ y) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef9 ef79 | exact superpose ef79 ef9
  have ef111 :
      x ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ ((y ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇
      (x ◇ (x ◇ (x ◇ x)))))) ◇ (y ◇ (((x ◇ (x ◇ (x ◇ x))) ◇
      ((y ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇
      ((y ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef9 ef95 | exact superpose ef95 ef9
  have ef127 :
      x ≠ ((x ◇ (x ◇ (x ◇ x))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇
      (x ◇ (x ◇ (x ◇ x)))))) ◇ (y ◇ (((x ◇ (x ◇ (x ◇ x))) ◇
      ((y ◇ (x ◇ (y ◇ y))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇
      ((y ◇ (x ◇ (y ◇ y))) ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef9 ef111 | exact superpose ef111 ef9
  have ef143 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef147 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef586 (X0 : G) :
      x ≠ (X0 ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (X0 ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇ (y ◇
      ((X0 ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (X0 ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      (X0 ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (X0 ◇ (x ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef143 ef127 | exact superpose ef127 ef143
  have ef607 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    first | exact superpose ef143 ef10 | exact superpose ef10 ef143
  have ef620 :
      x ≠ (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ x)) ◇
      (y ◇ ((x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ x)) ◇ (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ x)))) := by
    first | exact superpose ef607 ef586 | exact superpose ef586 ef607
  have ef636 :
      x ≠ (x ◇ (x ◇ (y ◇ (x ◇ (y ◇ y))))) ◇
      (y ◇ ((x ◇ (x ◇ (y ◇ (x ◇ (y ◇ y))))) ◇ (x ◇ (x ◇ (y ◇ (x ◇ (y ◇ y))))))) := by
    first | exact superpose ef147 ef620 | exact superpose ef620 ef147
  have ef638 : x ≠ (x ◇ y) ◇ (y ◇ ((x ◇ y) ◇ (x ◇ y))) := by
    first | exact superpose ef5 ef636 | exact superpose ef636 ef5
  subsumption ef638 ef5

theorem Equation879_termStructuralFrom_Equation556 :
    Law879.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law879.models_iff]
    exact fun x y ↦ @aux556_879 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 910 `x = y ◇ ((y ◇ x) ◇ (y ◇ y))` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_910 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ y)) ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇
      x)) ◇ (((y ◇ y) ◇ y) ◇ y)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ y)) ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇
      x)) ◇ (((y ◇ y) ◇ y) ◇ y)) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef30 :
      x ≠ (((((((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      ((y ◇ (y ◇ y)) ◇ y)) ◇ (((((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      ((y ◇ (y ◇ y)) ◇ y))) ◇ y) ◇ (((((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇
      x)) ◇ ((y ◇ (y ◇ y)) ◇ y)) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef31 :
      x ≠ (((((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ ((y ◇ (y ◇ y)) ◇
      y)) ◇ (((((((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      ((y ◇ (y ◇ y)) ◇ y)) ◇ (((((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      ((y ◇ (y ◇ y)) ◇ y))) ◇ y) := by
    first | exact superpose ef9 ef30 | exact superpose ef30 ef9
  have ef47 :
      x ≠ (((((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ ((y ◇ (y ◇ y)) ◇
      y)) ◇ (y ◇ ((((((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      ((y ◇ (y ◇ y)) ◇ y)) ◇ (((((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇
      ((y ◇ (y ◇ y)) ◇ y)))) := by
    first | exact superpose ef9 ef31 | exact superpose ef31 ef9
  have ef63 :
      x ≠ (((y ◇ (y ◇ y)) ◇ y) ◇ ((((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇
      x))) ◇ (y ◇ ((((y ◇ (y ◇ y)) ◇ y) ◇
      ((((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x))) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇
      ((((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ (((x ◇ x) ◇ y) ◇ x))))) := by
    first | exact superpose ef9 ef47 | exact superpose ef47 ef9
  have ef79 :
      x ≠ (((y ◇ (y ◇ y)) ◇ y) ◇ ((((x ◇ x) ◇ y) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇
      ((y ◇ (y ◇ y)) ◇ y)))) ◇ (y ◇ ((((y ◇ (y ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)))) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇
      ((((x ◇ x) ◇ y) ◇ x) ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)))))) := by
    first | exact superpose ef9 ef63 | exact superpose ef63 ef9
  have ef95 :
      x ≠ ((y ◇ (y ◇ (y ◇ y))) ◇ ((((x ◇ x) ◇ y) ◇ x) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇
      (y ◇ (y ◇ (y ◇ y)))))) ◇ (y ◇ (((y ◇ (y ◇ (y ◇ y))) ◇
      ((((x ◇ x) ◇ y) ◇ x) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ y)))))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇
      ((((x ◇ x) ◇ y) ◇ x) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ y)))))))) := by
    first | exact superpose ef9 ef79 | exact superpose ef79 ef9
  have ef111 :
      x ≠ ((y ◇ (y ◇ (y ◇ y))) ◇ ((x ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇
      (y ◇ (y ◇ (y ◇ y)))))) ◇ (y ◇ (((y ◇ (y ◇ (y ◇ y))) ◇
      ((x ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ y)))))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇
      ((x ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ y)))))))) := by
    first | exact superpose ef9 ef95 | exact superpose ef95 ef9
  have ef127 :
      x ≠ ((y ◇ (y ◇ (y ◇ y))) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇
      (y ◇ (y ◇ (y ◇ y)))))) ◇ (y ◇ (((y ◇ (y ◇ (y ◇ y))) ◇
      ((x ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ y)))))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇
      ((x ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (y ◇ y)))))))) := by
    first | exact superpose ef9 ef111 | exact superpose ef111 ef9
  have ef143 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef588 (X0 : G) :
      x ≠ ((X0 ◇ (y ◇ (X0 ◇ y))) ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ ((X0 ◇ (y ◇ (X0 ◇ y))) ◇
      (X0 ◇ (y ◇ (X0 ◇ y)))))) ◇ (y ◇ (((X0 ◇ (y ◇ (X0 ◇ y))) ◇
      ((x ◇ (y ◇ (x ◇ x))) ◇ ((X0 ◇ (y ◇ (X0 ◇ y))) ◇ (X0 ◇ (y ◇ (X0 ◇ y)))))) ◇
      ((X0 ◇ (y ◇ (X0 ◇ y))) ◇
      ((x ◇ (y ◇ (x ◇ x))) ◇ ((X0 ◇ (y ◇ (X0 ◇ y))) ◇ (X0 ◇ (y ◇ (X0 ◇ y)))))))) := by
    first | exact superpose ef143 ef127 | exact superpose ef127 ef143
  have ef607 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    first | exact superpose ef143 ef10 | exact superpose ef10 ef143
  have ef618 (X0 : G) : x ≠ (x ◇ (y ◇ (x ◇ x))) ◇ (y ◇ (X0 ◇ (y ◇ (X0 ◇ y)))) := by
    first | exact superpose ef607 ef588 | exact superpose ef588 ef607
  have ef636 : x ≠ (x ◇ (y ◇ (x ◇ x))) ◇ y := by
    first | exact superpose ef10 ef618 | exact superpose ef618 ef10
  have ef641 : x ≠ y ◇ (x ◇ (y ◇ (x ◇ x))) := by
    first | exact superpose ef9 ef636 | exact superpose ef636 ef9
  subsumption ef641 ef5

theorem Equation910_termStructuralFrom_Equation556 :
    Law910.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law910.models_iff]
    exact fun x y ↦ @aux556_910 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 917 `x = y ◇ ((y ◇ y) ◇ (x ◇ y))` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_917 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      (((y ◇ y) ◇ x) ◇ y)) ◇ ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      (((y ◇ y) ◇ x) ◇ y))) ◇ y) ◇ ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇
      y)) ◇ (((y ◇ y) ◇ x) ◇ y)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      (((y ◇ y) ◇ x) ◇ y)) ◇ ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      (((y ◇ y) ◇ x) ◇ y))) ◇ y) ◇ ((((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇
      y)) ◇ (((y ◇ y) ◇ x) ◇ y)) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef28 :
      x ≠ (((((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((x ◇ (y ◇ y)) ◇ y)) ◇ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((x ◇ (y ◇ y)) ◇ y))) ◇ y) ◇ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇
      y)) ◇ ((x ◇ (y ◇ y)) ◇ y)) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef31 :
      x ≠ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ ((x ◇ (y ◇ y)) ◇
      y)) ◇ (((((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((x ◇ (y ◇ y)) ◇ y)) ◇ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((x ◇ (y ◇ y)) ◇ y))) ◇ y) := by
    first | exact superpose ef9 ef28 | exact superpose ef28 ef9
  have ef47 :
      x ≠ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ ((x ◇ (y ◇ y)) ◇
      y)) ◇ (y ◇ ((((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((x ◇ (y ◇ y)) ◇ y)) ◇ (((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇
      ((x ◇ (y ◇ y)) ◇ y)))) := by
    first | exact superpose ef9 ef31 | exact superpose ef31 ef9
  have ef63 :
      x ≠ (((x ◇ (y ◇ y)) ◇ y) ◇ ((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇
      y))) ◇ (y ◇ ((((x ◇ (y ◇ y)) ◇ y) ◇
      ((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ (((x ◇ (y ◇ y)) ◇ y) ◇
      ((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))))) := by
    first | exact superpose ef9 ef47 | exact superpose ef47 ef9
  have ef79 :
      x ≠ (((x ◇ (y ◇ y)) ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (((x ◇ (y ◇ y)) ◇ y) ◇
      ((x ◇ (y ◇ y)) ◇ y)))) ◇ (y ◇ ((((x ◇ (y ◇ y)) ◇ y) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)))) ◇ (((x ◇ (y ◇ y)) ◇ y) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)))))) := by
    first | exact superpose ef9 ef63 | exact superpose ef63 ef9
  have ef95 :
      x ≠ ((y ◇ (x ◇ (y ◇ y))) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇
      (y ◇ (x ◇ (y ◇ y)))))) ◇ (y ◇ (((y ◇ (x ◇ (y ◇ y))) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))))) := by
    first | exact superpose ef9 ef79 | exact superpose ef79 ef9
  have ef111 :
      x ≠ ((y ◇ (x ◇ (y ◇ y))) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇
      (y ◇ (x ◇ (y ◇ y)))))) ◇ (y ◇ (((y ◇ (x ◇ (y ◇ y))) ◇
      ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇
      ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))))) := by
    first | exact superpose ef9 ef95 | exact superpose ef95 ef9
  have ef127 :
      x ≠ ((y ◇ (x ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇
      (y ◇ (x ◇ (y ◇ y)))))) ◇ (y ◇ (((y ◇ (x ◇ (y ◇ y))) ◇
      ((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇
      ((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y)))))))) := by
    first | exact superpose ef9 ef111 | exact superpose ef111 ef9
  have ef143 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef147 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef584 (X0 : G) :
      x ≠ (X0 ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (X0 ◇ (y ◇ (x ◇ (y ◇ y)))))) ◇ (y ◇
      ((X0 ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (X0 ◇ (y ◇ (x ◇ (y ◇ y)))))) ◇
      (X0 ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (X0 ◇ (y ◇ (x ◇ (y ◇ y)))))))) := by
    first | exact superpose ef143 ef127 | exact superpose ef127 ef143
  have ef607 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    first | exact superpose ef143 ef10 | exact superpose ef10 ef143
  have ef620 :
      x ≠ (x ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ y)) ◇
      (y ◇ ((x ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ y)) ◇ (x ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ y)))) := by
    first | exact superpose ef607 ef584 | exact superpose ef584 ef607
  have ef636 :
      x ≠ (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ y))))) ◇
      (y ◇ ((x ◇ (y ◇ (y ◇ (y ◇ (y ◇ y))))) ◇ (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ y))))))) := by
    first | exact superpose ef147 ef620 | exact superpose ef620 ef147
  have ef638 : x ≠ (x ◇ y) ◇ (y ◇ ((x ◇ y) ◇ (x ◇ y))) := by
    first | exact superpose ef5 ef636 | exact superpose ef636 ef5
  subsumption ef638 ef5

theorem Equation917_termStructuralFrom_Equation556 :
    Law917.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law917.models_iff]
    exact fun x y ↦ @aux556_917 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 1045 `x = x ◇ ((y ◇ (y ◇ x)) ◇ x)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1045 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((x ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ x) ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ x) ◇ x) ◇
      x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef27 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef259 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef301 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X1)) = X3 := by
    first | exact superpose ef10 ef27 | exact superpose ef27 ef10
  have ef303 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef27 ef27
  have ef320 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef27 ef10 | exact superpose ef10 ef27
  have ef345 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef259 ef259
  have ef384 :
      x ≠ ((x ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) := by
    first | exact superpose ef259 ef6 | exact superpose ef6 ef259
  have ef396 :
      x ≠ ((x ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇ x)) ◇
      (x ◇ (((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇
      x)) := by
    first | exact superpose ef259 ef384 | exact superpose ef384 ef259
  have ef409 :
      x ≠ ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x)) := by
    first | exact superpose ef320 ef396 | exact superpose ef396 ef320
  have ef421 :
      x ≠ ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇
      x)) ◇ (x ◇
      ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x))) := by
    first | exact superpose ef345 ef409 | exact superpose ef409 ef345
  have ef433 :
      x ≠ ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇
      x)) ◇ (x ◇ (x ◇
      (((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x)))) := by
    first | exact superpose ef259 ef421 | exact superpose ef421 ef259
  have ef445 :
      x ≠ ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇
      ((x ◇ (((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x)) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x)))) := by
    first | exact superpose ef27 ef433 | exact superpose ef433 ef27
  have ef457 :
      x ≠ ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (x ◇
      (((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x))) := by
    first | exact superpose ef345 ef445 | exact superpose ef445 ef345
  have ef469 :
      x ≠ ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (x ◇
      (x ◇ ((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x)))) := by
    first | exact superpose ef259 ef457 | exact superpose ef457 ef259
  have ef481 :
      x ≠ ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (x ◇
      (x ◇ (x ◇ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))))))) := by
    first | exact superpose ef259 ef469 | exact superpose ef469 ef259
  have ef493 :
      x ≠ ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (x ◇
      (x ◇ (x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))))))) := by
    first | exact superpose ef345 ef481 | exact superpose ef481 ef345
  have ef505 :
      x ≠ ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇ (x ◇
      (x ◇ (x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (((y ◇ x) ◇ x) ◇ x)))))))) := by
    first | exact superpose ef345 ef493 | exact superpose ef493 ef345
  have ef517 :
      x ≠ ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ (((x ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (x ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef303 ef505 | exact superpose ef505 ef303
  have ef529 :
      x ≠ ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇
      ((x ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) := by
    first | exact superpose ef345 ef517 | exact superpose ef517 ef345
  have ef541 :
      x ≠ ((((((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇
      ((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef345 ef529 | exact superpose ef529 ef345
  have ef553 :
      x ≠ ((((((y ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇
      ((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (x ◇ ((y ◇ x) ◇ x)))))) := by
    first | exact superpose ef259 ef541 | exact superpose ef541 ef259
  have ef565 :
      x ≠ ((((((y ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ x) := by
    first | exact superpose ef303 ef553 | exact superpose ef553 ef303
  have ef577 :
      x ≠ ((((((y ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef259 ef565 | exact superpose ef565 ef259
  have ef589 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇
      ((((((y ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x) ◇
      x) := by
    first | exact superpose ef320 ef577 | exact superpose ef577 ef320
  have ef601 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ (x ◇
      (((((y ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x) ◇ x)) := by
    first | exact superpose ef259 ef589 | exact superpose ef589 ef259
  have ef613 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ (x ◇
      (x ◇ ((((y ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ x))) := by
    first | exact superpose ef259 ef601 | exact superpose ef601 ef259
  have ef625 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ (x ◇
      (x ◇ (x ◇ (((y ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((y ◇ x) ◇ x)))))) := by
    first | exact superpose ef259 ef613 | exact superpose ef613 ef259
  have ef637 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ (x ◇
      (x ◇ (x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ (((y ◇ x) ◇ x) ◇ x)))))) := by
    first | exact superpose ef345 ef625 | exact superpose ef625 ef345
  have ef649 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ (x ◇
      (x ◇ (x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (x ◇ ((y ◇ x) ◇ x)))))))) := by
    first | exact superpose ef345 ef637 | exact superpose ef637 ef345
  have ef661 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ (x ◇
      (x ◇ (x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (y ◇ x))))))))) := by
    first | exact superpose ef259 ef649 | exact superpose ef649 ef259
  have ef673 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ (x ◇
      (x ◇ (x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))))))) := by
    first | exact superpose ef259 ef661 | exact superpose ef661 ef259
  have ef685 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ (x ◇
      (x ◇ (x ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))))))) := by
    first | exact superpose ef9 ef673 | exact superpose ef673 ef9
  have ef697 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ (x ◇
      (x ◇ (x ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))))))) := by
    first | exact superpose ef259 ef685 | exact superpose ef685 ef259
  have ef709 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ (x ◇
      (x ◇ (x ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))))))) := by
    first | exact superpose ef259 ef697 | exact superpose ef697 ef259
  have ef721 : x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef301 ef709 | exact superpose ef709 ef301
  have ef733 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ x) := by
    first | exact superpose ef320 ef721 | exact superpose ef721 ef320
  have ef745 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef259 ef733 | exact superpose ef733 ef259
  have ef757 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))) := by
    first | exact superpose ef259 ef745 | exact superpose ef745 ef259
  have ef769 : x ≠ ((x ◇ (x ◇ x)) ◇ x) ◇ x := by
    first | exact superpose ef5 ef757 | exact superpose ef757 ef5
  have ef781 : x ≠ x ◇ ((x ◇ (x ◇ x)) ◇ x) := by
    first | exact superpose ef9 ef769 | exact superpose ef769 ef9
  have ef793 : x ≠ x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef259 ef781 | exact superpose ef781 ef259
  subsumption ef793 ef5

theorem Equation1045_termStructuralFrom_Equation556 :
    Law1045.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1045.models_iff]
    exact fun x y ↦ @aux556_1045 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 1075 `x = y ◇ ((x ◇ (x ◇ y)) ◇ x)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1075 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((y ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((y ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇
      x) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef28 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef219 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef243 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X1)) = X3 := by
    first | exact superpose ef9 ef7 | exact superpose ef7 ef9
  have ef263 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef28 ef28
  have ef280 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef28 ef10 | exact superpose ef10 ef28
  have ef305 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef219 ef219
  have ef346 :
      x ≠ ((y ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) := by
    first | exact superpose ef219 ef6 | exact superpose ef6 ef219
  have ef356 :
      x ≠ ((y ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇ x)) ◇
      (x ◇ (((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇
      x)) := by
    first | exact superpose ef219 ef346 | exact superpose ef346 ef219
  have ef369 :
      x ≠ ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((y ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x)) := by
    first | exact superpose ef280 ef356 | exact superpose ef356 ef280
  have ef381 :
      x ≠ ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇
      x)) ◇ (y ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x))) := by
    first | exact superpose ef305 ef369 | exact superpose ef369 ef305
  have ef393 :
      x ≠ ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇
      x)) ◇ (y ◇ (x ◇
      (((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x)))) := by
    first | exact superpose ef219 ef381 | exact superpose ef381 ef219
  have ef405 :
      x ≠ ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (x ◇
      ((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x))) ◇ (y ◇ (x ◇
      (x ◇ ((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x))))) := by
    first | exact superpose ef219 ef393 | exact superpose ef393 ef219
  have ef417 :
      x ≠ ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (x ◇
      (x ◇ (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y)))))) ◇ (y ◇ (x ◇
      (x ◇ (x ◇ (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y)))))))) := by
    first | exact superpose ef219 ef405 | exact superpose ef405 ef219
  have ef429 :
      x ≠ ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (x ◇
      (x ◇ ((((x ◇ y) ◇ y) ◇ y) ◇ ((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)))))) ◇ (y ◇ (x ◇
      (x ◇ (x ◇ ((((x ◇ y) ◇ y) ◇ y) ◇ ((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)))))))) := by
    first | exact superpose ef305 ef417 | exact superpose ef417 ef305
  have ef441 :
      x ≠ ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (x ◇
      (x ◇ ((((x ◇ y) ◇ y) ◇ y) ◇ ((y ◇ ((x ◇ y) ◇ y)) ◇ (x ◇ (((x ◇ y) ◇ y) ◇ y))))))) ◇ (y ◇ (x ◇
      (x ◇ (x ◇ ((((x ◇ y) ◇ y) ◇ y) ◇ ((y ◇ ((x ◇ y) ◇ y)) ◇ (x ◇ (((x ◇ y) ◇ y) ◇ y))))))))) := by
    first | exact superpose ef305 ef429 | exact superpose ef429 ef305
  have ef453 :
      x ≠ ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))) := by
    first | exact superpose ef263 ef441 | exact superpose ef441 ef263
  have ef465 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇
      ((((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) := by
    first | exact superpose ef280 ef453 | exact superpose ef453 ef280
  have ef477 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇
      (((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x) ◇ x)) := by
    first | exact superpose ef219 ef465 | exact superpose ef465 ef219
  have ef489 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇
      (x ◇ ((((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y))) ◇ x))) := by
    first | exact superpose ef219 ef477 | exact superpose ef477 ef219
  have ef501 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇
      (x ◇ (x ◇ (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ y) ◇ y)))))) := by
    first | exact superpose ef219 ef489 | exact superpose ef489 ef219
  have ef513 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇
      (x ◇ (x ◇ ((((x ◇ y) ◇ y) ◇ y) ◇ ((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)))))) := by
    first | exact superpose ef305 ef501 | exact superpose ef501 ef305
  have ef525 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇
      (x ◇ (x ◇ ((((x ◇ y) ◇ y) ◇ y) ◇ ((y ◇ ((x ◇ y) ◇ y)) ◇ (x ◇ (((x ◇ y) ◇ y) ◇ y))))))) := by
    first | exact superpose ef305 ef513 | exact superpose ef513 ef305
  have ef537 : x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y))) := by
    first | exact superpose ef263 ef525 | exact superpose ef525 ef263
  have ef549 : x ≠ ((x ◇ (x ◇ y)) ◇ x) ◇ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) := by
    first | exact superpose ef280 ef537 | exact superpose ef537 ef280
  have ef561 : x ≠ ((x ◇ (x ◇ y)) ◇ x) ◇ (((x ◇ (x ◇ y)) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))) := by
    first | exact superpose ef305 ef549 | exact superpose ef549 ef305
  have ef573 : x ≠ ((x ◇ (y ◇ x)) ◇ x) ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (y ◇ x))))) := by
    first | exact superpose ef219 ef561 | exact superpose ef561 ef219
  have ef585 : x ≠ (x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (y ◇ x))))) := by
    first | exact superpose ef9 ef573 | exact superpose ef573 ef9
  subsumption ef585 ef243

theorem Equation1075_termStructuralFrom_Equation556 :
    Law1075.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1075.models_iff]
    exact fun x y ↦ @aux556_1075 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 1086 `x = y ◇ ((x ◇ (y ◇ y)) ◇ y)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1086 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((y ◇
      ((((((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ y) ◇ y) ◇ y)) ◇
      ((((((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ y) ◇ y) ◇ y)) ◇
      ((((((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ y) ◇ y) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((y ◇
      ((((((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ y) ◇ y) ◇ y)) ◇
      ((((((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ y) ◇ y) ◇ y)) ◇
      ((((((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ y) ◇ y) ◇
      y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef26 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef31 :
      x ≠ ((y ◇
      (((y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇ y)) ◇
      (((y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇ y)) ◇
      (((y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      y) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef33 :
      x ≠ (((y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      y) ◇ ((y ◇
      (((y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇ y)) ◇
      (((y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      y)) := by
    first | exact superpose ef9 ef31 | exact superpose ef31 ef9
  have ef51 :
      x ≠ (((y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      y) ◇ ((((y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      y) ◇ (y ◇
      (((y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) ◇
      y))) := by
    first | exact superpose ef9 ef33 | exact superpose ef33 ef9
  have ef69 :
      x ≠ (y ◇ ((y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      y)) ◇ ((y ◇ ((y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      y)) ◇ (y ◇ (y ◇
      ((y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y)))) := by
    first | exact superpose ef9 ef51 | exact superpose ef51 ef9
  have ef87 :
      x ≠ (y ◇ (y ◇ (y ◇
      (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ ((y ◇ (y ◇
      (y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇ (y ◇ (y ◇
      (y ◇ (y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))))))) := by
    first | exact superpose ef9 ef69 | exact superpose ef69 ef9
  have ef105 :
      x ≠ (y ◇
      (y ◇ (y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      ((y ◇ (y ◇ (y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef10 ef87 | exact superpose ef87 ef10
  have ef123 :
      x ≠ (y ◇ (y ◇
      (y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))))) ◇
      ((((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (y ◇
      (y ◇ (y ◇ (((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)))))) := by
    first | exact superpose ef9 ef105 | exact superpose ef105 ef9
  have ef141 :
      x ≠ (y ◇ (y ◇
      (y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ (y ◇
      (y ◇ (y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((x ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))))))) := by
    first | exact superpose ef9 ef123 | exact superpose ef123 ef9
  have ef159 :
      x ≠ (y ◇ (y ◇
      (y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (x ◇ (((y ◇ y) ◇ y) ◇ y))))))) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (x ◇ (((y ◇ y) ◇ y) ◇ y)))) ◇ (y ◇
      (y ◇ (y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (x ◇ (((y ◇ y) ◇ y) ◇ y)))))))) := by
    first | exact superpose ef9 ef141 | exact superpose ef141 ef9
  have ef177 :
      x ≠ (y ◇ (y ◇
      (y ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (x ◇ (y ◇ ((y ◇ y) ◇ y)))))))) ◇
      (((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (x ◇ (y ◇ ((y ◇ y) ◇ y))))) ◇ (y ◇
      (y ◇ (y ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (x ◇ (y ◇ ((y ◇ y) ◇ y))))))))) := by
    first | exact superpose ef9 ef159 | exact superpose ef159 ef9
  have ef195 :
      x ≠ (y ◇ (y ◇
      (y ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (x ◇ (y ◇ (y ◇ (y ◇ y))))))))) ◇
      (((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))) ◇ (y ◇
      (y ◇ (y ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))))))) := by
    first | exact superpose ef9 ef177 | exact superpose ef177 ef9
  have ef213 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef217 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef278 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef26 ef10 | exact superpose ef10 ef26
  have ef303 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef217 ef217
  have ef705 (X0 X1 X2 X3 X4 : G) :
      X4 ◇ (X2 ◇ X0) = X1 ◇ (X2 ◇ ((X3 ◇ ((X0 ◇ X3) ◇ X4)) ◇ X1)) := by
    first | exact superpose ef26 ef213 | exact superpose ef213 ef26
  have ef739 (X0 X1 X2 X3 : G) : X3 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X1 := by
    first | exact superpose ef213 ef5 | exact superpose ef5 ef213
  have ef747 (X0 : G) :
      x ≠ (y ◇ (y ◇ (y ◇ (X0 ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (X0 ◇ x)))))) ◇
      ((X0 ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (X0 ◇ x))) ◇
      (y ◇ (y ◇ (y ◇ (X0 ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (X0 ◇ x))))))) := by
    first | exact superpose ef213 ef195 | exact superpose ef195 ef213
  have ef752 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ X4) = X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    first | exact superpose ef213 ef10 | exact superpose ef10 ef213
  have ef789 (X0 : G) :
      x ≠ ((y ◇ (y ◇ (y ◇ y))) ◇ (x ◇ y)) ◇
      ((X0 ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (X0 ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (x ◇ y))) := by
    first | exact superpose ef752 ef747 | exact superpose ef747 ef752
  have ef805 (X0 : G) :
      x ≠ ((y ◇ (y ◇ (y ◇ y))) ◇ (x ◇ y)) ◇
      (((x ◇ y) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ (X0 ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (X0 ◇ x)))) := by
    first | exact superpose ef303 ef789 | exact superpose ef789 ef303
  have ef810 (X0 : G) :
      x ≠ ((y ◇ (y ◇ (y ◇ y))) ◇ (y ◇ x)) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ (X0 ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (X0 ◇ x)))) := by
    first | exact superpose ef9 ef805 | exact superpose ef805 ef9
  have ef814 (X0 : G) :
      x ≠ ((x ◇ y) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ (X0 ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (X0 ◇ x)))) := by
    first | exact superpose ef278 ef810 | exact superpose ef810 ef278
  have ef815 (X0 : G) :
      x ≠ ((y ◇ x) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇
      (((y ◇ x) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ (X0 ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (X0 ◇ x)))) := by
    first | exact superpose ef9 ef814 | exact superpose ef814 ef9
  have ef828 (X0 : G) :
      x ≠ X0 ◇ (((y ◇ x) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇
      (((y ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ x) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ x)) ◇ X0)) := by
    first | exact superpose ef213 ef815 | exact superpose ef815 ef213
  have ef829 : x ≠ x ◇ (((y ◇ x) ◇ (y ◇ (y ◇ (y ◇ y)))) ◇ (y ◇ x)) := by
    first | exact superpose ef705 ef828 | exact superpose ef828 ef705
  have ef830 : x ≠ x ◇ ((x ◇ y) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ (y ◇ y))))) := by
    first | exact superpose ef303 ef829 | exact superpose ef829 ef303
  have ef831 : x ≠ x ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ (y ◇ (y ◇ (y ◇ y))))) := by
    first | exact superpose ef9 ef830 | exact superpose ef830 ef9
  have ef1022 (X0 : G) : x ≠ x ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ (X0 ◇ (y ◇ (y ◇ X0))))) := by
    first | exact superpose ef213 ef831 | exact superpose ef831 ef213
  have ef1193 (X0 : G) : x ≠ x ◇ ((y ◇ x) ◇ (X0 ◇ (x ◇ (X0 ◇ y)))) := by
    first | exact superpose ef213 ef1022 | exact superpose ef1022 ef213
  subsumption ef1193 ef739

theorem Equation1086_termStructuralFrom_Equation556 :
    Law1086.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1086.models_iff]
    exact fun x y ↦ @aux556_1086 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 1122 `x = y ◇ ((y ◇ (y ◇ y)) ◇ x)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1122 [Magma G] (h : Equation556 G) (x y : G) :
    x = ((y ◇
      ((((((y ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((y ◇
      ((((((y ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇
      x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef27 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef32 :
      x ≠ ((y ◇
      ((((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef33 :
      x ≠ ((((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((y ◇
      ((((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x)) := by
    first | exact superpose ef9 ef32 | exact superpose ef32 ef9
  have ef51 :
      x ≠ ((((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ (((((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ (y ◇
      ((((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x))) := by
    first | exact superpose ef9 ef33 | exact superpose ef33 ef9
  have ef69 :
      x ≠ (x ◇ (((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x) ◇
      x)) ◇ ((x ◇ (((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x) ◇
      x)) ◇ (y ◇ (x ◇
      (((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x) ◇ x)))) := by
    first | exact superpose ef9 ef51 | exact superpose ef51 ef9
  have ef87 :
      x ≠ (x ◇ (x ◇ ((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇
      x))) ◇ ((x ◇ (x ◇
      ((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x))) ◇ (y ◇ (x ◇
      (x ◇ ((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ x))))) := by
    first | exact superpose ef9 ef69 | exact superpose ef69 ef9
  have ef105 :
      x ≠ (x ◇ (x ◇ (x ◇
      (((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y)))))) ◇ ((x ◇ (x ◇
      (x ◇ (((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y)))))) ◇ (y ◇ (x ◇
      (x ◇ (x ◇ (((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y)))))))) := by
    first | exact superpose ef9 ef87 | exact superpose ef87 ef9
  have ef123 :
      x ≠ (x ◇ (x ◇ (x ◇
      ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))))))) ◇ ((x ◇ (x ◇
      (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))))))) ◇ (y ◇ (x ◇
      (x ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))))))))) := by
    first | exact superpose ef9 ef105 | exact superpose ef105 ef9
  have ef141 :
      x ≠ (x ◇ (x ◇ (x ◇
      ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y)))))))) ◇ ((x ◇ (x ◇
      (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y)))))))) ◇ (y ◇ (x ◇
      (x ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y)))))))))) := by
    first | exact superpose ef9 ef123 | exact superpose ef123 ef9
  have ef159 :
      x ≠ (x ◇ (x ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ y))))) ◇
      ((x ◇ (x ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ y))))) ◇
      (y ◇ (x ◇ (x ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ y))))))) := by
    first | exact superpose ef27 ef141 | exact superpose ef141 ef27
  have ef177 :
      x ≠ (x ◇ (x ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y))))))) ◇
      ((x ◇ (x ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y))))))) ◇
      (y ◇ (x ◇ (x ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y))))))))) := by
    first | exact superpose ef9 ef159 | exact superpose ef159 ef9
  have ef195 :
      x ≠ (x ◇ (x ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ y)))) ◇
      ((x ◇ (x ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ y)))) ◇
      (y ◇ (x ◇ (x ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ y)))))) := by
    first | exact superpose ef27 ef177 | exact superpose ef177 ef27
  have ef213 :
      x ≠ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y)))))) ◇
      ((x ◇ (x ◇ (x ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y)))))) ◇
      (y ◇ (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y)))))))) := by
    first | exact superpose ef9 ef195 | exact superpose ef195 ef9
  have ef231 : x ≠ (x ◇ (x ◇ (x ◇ y))) ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))) := by
    first | exact superpose ef27 ef213 | exact superpose ef213 ef27
  have ef249 : x ≠ (x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (y ◇ x))))) := by
    first | exact superpose ef9 ef231 | exact superpose ef231 ef9
  have ef269 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef315 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X1)) = X3 := by
    first | exact superpose ef10 ef27 | exact superpose ef27 ef10
  have ef808 (X0 : G) :
      x ≠ (X0 ◇ (x ◇ (X0 ◇ y))) ◇ ((X0 ◇ (x ◇ (X0 ◇ y))) ◇ (y ◇ (X0 ◇ (x ◇ (X0 ◇ y))))) := by
    first | exact superpose ef269 ef249 | exact superpose ef249 ef269
  subsumption ef808 ef315

theorem Equation1122_termStructuralFrom_Equation556 :
    Law1122.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1122.models_iff]
    exact fun x y ↦ @aux556_1122 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 1184 `x = y ◇ ((z ◇ (z ◇ y)) ◇ x)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1184 [Magma G] (h : Equation556 G) (x y z : G) :
    x = ((y ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((y ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇ x)) ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) ◇
      x) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef28 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef219 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef243 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X1)) = X3 := by
    first | exact superpose ef9 ef7 | exact superpose ef7 ef9
  have ef263 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef28 ef28
  have ef280 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef28 ef10 | exact superpose ef10 ef28
  have ef305 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef219 ef219
  have ef346 :
      x ≠ ((y ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) := by
    first | exact superpose ef219 ef6 | exact superpose ef6 ef219
  have ef356 :
      x ≠ ((y ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇ x)) ◇
      (x ◇ (((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇
      x)) := by
    first | exact superpose ef219 ef346 | exact superpose ef346 ef219
  have ef369 :
      x ≠ ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((y ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇ x)) ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x)) := by
    first | exact superpose ef280 ef356 | exact superpose ef356 ef280
  have ef381 :
      x ≠ ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇
      x)) ◇ (y ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x))) := by
    first | exact superpose ef305 ef369 | exact superpose ef369 ef305
  have ef393 :
      x ≠ ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇
      x)) ◇ (y ◇ (x ◇
      (((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x)))) := by
    first | exact superpose ef219 ef381 | exact superpose ef381 ef219
  have ef405 :
      x ≠ ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (x ◇
      ((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x))) ◇ (y ◇ (x ◇
      (x ◇ ((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x))))) := by
    first | exact superpose ef219 ef393 | exact superpose ef393 ef219
  have ef417 :
      x ≠ ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (x ◇
      (x ◇ (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y)))))) ◇ (y ◇ (x ◇
      (x ◇ (x ◇ (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y)))))))) := by
    first | exact superpose ef219 ef405 | exact superpose ef405 ef219
  have ef429 :
      x ≠ ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (x ◇
      (x ◇ ((((z ◇ y) ◇ y) ◇ y) ◇ ((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)))))) ◇ (y ◇ (x ◇
      (x ◇ (x ◇ ((((z ◇ y) ◇ y) ◇ y) ◇ ((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)))))))) := by
    first | exact superpose ef305 ef417 | exact superpose ef417 ef305
  have ef441 :
      x ≠ ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (x ◇
      (x ◇ ((((z ◇ y) ◇ y) ◇ y) ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ (z ◇ (((z ◇ y) ◇ y) ◇ y))))))) ◇ (y ◇ (x ◇
      (x ◇ (x ◇ ((((z ◇ y) ◇ y) ◇ y) ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ (z ◇ (((z ◇ y) ◇ y) ◇ y))))))))) := by
    first | exact superpose ef305 ef429 | exact superpose ef429 ef305
  have ef453 :
      x ≠ ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))) := by
    first | exact superpose ef263 ef441 | exact superpose ef441 ef263
  have ef465 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇
      ((((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x) ◇
      x) := by
    first | exact superpose ef280 ef453 | exact superpose ef453 ef280
  have ef477 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇
      (((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x) ◇ x)) := by
    first | exact superpose ef219 ef465 | exact superpose ef465 ef219
  have ef489 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇
      (x ◇ ((((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y))) ◇ x))) := by
    first | exact superpose ef219 ef477 | exact superpose ef477 ef219
  have ef501 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇
      (x ◇ (x ◇ (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((z ◇ y) ◇ y)))))) := by
    first | exact superpose ef219 ef489 | exact superpose ef489 ef219
  have ef513 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇
      (x ◇ (x ◇ ((((z ◇ y) ◇ y) ◇ y) ◇ ((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)))))) := by
    first | exact superpose ef305 ef501 | exact superpose ef501 ef305
  have ef525 :
      x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇
      (x ◇ (x ◇ ((((z ◇ y) ◇ y) ◇ y) ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ (z ◇ (((z ◇ y) ◇ y) ◇ y))))))) := by
    first | exact superpose ef305 ef513 | exact superpose ef513 ef305
  have ef537 : x ≠ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y))) := by
    first | exact superpose ef263 ef525 | exact superpose ef525 ef263
  have ef549 : x ≠ ((x ◇ (x ◇ y)) ◇ x) ◇ ((y ◇ (x ◇ (x ◇ (x ◇ y)))) ◇ (x ◇ (x ◇ (x ◇ y)))) := by
    first | exact superpose ef280 ef537 | exact superpose ef537 ef280
  have ef561 : x ≠ ((x ◇ (x ◇ y)) ◇ x) ◇ (((x ◇ (x ◇ y)) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (x ◇ y))))) := by
    first | exact superpose ef305 ef549 | exact superpose ef549 ef305
  have ef573 : x ≠ ((x ◇ (y ◇ x)) ◇ x) ◇ (((x ◇ (y ◇ x)) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (y ◇ x))))) := by
    first | exact superpose ef219 ef561 | exact superpose ef561 ef219
  have ef585 : x ≠ (x ◇ (x ◇ (y ◇ x))) ◇ ((x ◇ (x ◇ (y ◇ x))) ◇ (y ◇ (x ◇ (x ◇ (y ◇ x))))) := by
    first | exact superpose ef9 ef573 | exact superpose ef573 ef9
  subsumption ef585 ef243

theorem Equation1184_termStructuralFrom_Equation556 :
    Law1184.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1184.models_iff]
    exact fun x y z ↦ @aux556_1184 G M h x y z
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 1629 `x = (x ◇ x) ◇ ((x ◇ x) ◇ x)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1629 [Magma G] (h : Equation556 G) (x : G) :
    x = (((((x ◇ x) ◇ x) ◇ x) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((x ◇ x) ◇ x) ◇ x) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef25 :
      x ≠ ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef28 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef30 :
      x ≠ ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ (((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef9 ef25 | exact superpose ef25 ef9
  have ef44 :
      x ≠ (x ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ ((x ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ (x ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)))) := by
    first | exact superpose ef9 ef30 | exact superpose ef30 ef9
  have ef58 :
      x ≠ (x ◇ (x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ x))) ◇ ((x ◇ (x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ (x ◇ (x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef9 ef44 | exact superpose ef44 ef9
  have ef72 : x ≠ ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))) := by
    first | exact superpose ef28 ef58 | exact superpose ef58 ef28
  have ef86 : x ≠ ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef9 ef72 | exact superpose ef72 ef9
  subsumption ef86 ef10

theorem Equation1629_termStructuralFrom_Equation556 :
    Law1629.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1629.models_iff]
    exact fun x ↦ @aux556_1629 G M h x
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 1632 `x = (x ◇ x) ◇ ((x ◇ y) ◇ y)` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1632 [Magma G] (h : Equation556 G) (x y : G) :
    x = (((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ y)) ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ y)) ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef28 :
      x ≠ (((y ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)))) ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇ (y ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y))) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef29 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇
      (((y ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)))) ◇
      (((x ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef9 ef28 | exact superpose ef28 ef9
  have ef43 :
      x ≠ (y ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇
      ((y ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y))))) := by
    first | exact superpose ef9 ef29 | exact superpose ef29 ef9
  have ef57 :
      x ≠ (y ◇ ((y ◇ y) ◇ (y ◇ ((y ◇ y) ◇ x)))) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇
      ((y ◇ ((y ◇ y) ◇ (y ◇ ((y ◇ y) ◇ x)))) ◇ (y ◇ ((y ◇ y) ◇ (y ◇ ((y ◇ y) ◇ x)))))) := by
    first | exact superpose ef9 ef43 | exact superpose ef43 ef9
  have ef71 : x ≠ x ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ (x ◇ x)) := by
    first | exact superpose ef10 ef57 | exact superpose ef57 ef10
  have ef85 : x ≠ x ◇ ((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef9 ef71 | exact superpose ef71 ef9
  have ef99 : x ≠ x ◇ ((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) := by
    first | exact superpose ef9 ef85 | exact superpose ef85 ef9
  subsumption ef99 ef10

theorem Equation1632_termStructuralFrom_Equation556 :
    Law1632.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1632.models_iff]
    exact fun x y ↦ @aux556_1632 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 1647 `x = (x ◇ y) ◇ ((x ◇ y) ◇ x)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1647 [Magma G] (h : Equation556 G) (x y : G) :
    x = (((((x ◇ y) ◇ y) ◇ y) ◇ ((((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇ ((((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((x ◇ y) ◇ y) ◇ y) ◇ ((((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇ ((((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef28 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef117 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef161 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef28 ef28
  have ef178 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef28 ef10 | exact superpose ef10 ef28
  have ef203 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef117 ef117
  have ef246 :
      x ≠ (((((x ◇ y) ◇ y) ◇ y) ◇ ((((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇ (x ◇ (((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x)) := by
    first | exact superpose ef117 ef6 | exact superpose ef6 ef117
  have ef247 :
      x ≠ ((((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x) ◇
      (((((x ◇ y) ◇ y) ◇ y) ◇ ((((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇
      ((((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef178 ef246 | exact superpose ef246 ef178
  have ef255 :
      x ≠ ((((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x)) ◇
      ((((x ◇ y) ◇ y) ◇ y) ◇ ((((((x ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef203 ef247 | exact superpose ef247 ef203
  subsumption ef255 ef161

theorem Equation1647_termStructuralFrom_Equation556 :
    Law1647.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1647.models_iff]
    exact fun x y ↦ @aux556_1647 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 1654 `x = (x ◇ y) ◇ ((y ◇ x) ◇ x)` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1654 [Magma G] (h : Equation556 G) (x y : G) :
    x = (((((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x)) ◇
      (((y ◇ y) ◇ x) ◇ y)) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x)) ◇
      (((y ◇ y) ◇ x) ◇ y)) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef21 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef28 :
      x ≠ (((((x ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇
      (((y ◇ y) ◇ x) ◇ y)) ◇ (((x ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ x) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef29 :
      x ≠ (((x ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ x) ◇
      (((((x ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇
      (((y ◇ y) ◇ x) ◇ y)) := by
    first | exact superpose ef9 ef28 | exact superpose ef28 ef9
  have ef43 :
      x ≠ (((x ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ x) ◇ ((((y ◇ y) ◇ x) ◇ y) ◇
      ((((x ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ x))) := by
    first | exact superpose ef9 ef29 | exact superpose ef29 ef9
  have ef57 :
      x ≠ (x ◇ ((x ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x))) ◇ ((((y ◇ y) ◇ x) ◇ y) ◇
      ((x ◇ ((x ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef9 ef43 | exact superpose ef43 ef9
  have ef71 : x ≠ y ◇ ((((y ◇ y) ◇ x) ◇ y) ◇ (y ◇ y)) := by
    first | exact superpose ef21 ef57 | exact superpose ef57 ef21
  have ef85 : x ≠ y ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) := by
    first | exact superpose ef9 ef71 | exact superpose ef71 ef9
  have ef99 : x ≠ y ◇ ((y ◇ y) ◇ (y ◇ ((y ◇ y) ◇ x))) := by
    first | exact superpose ef9 ef85 | exact superpose ef85 ef9
  subsumption ef99 ef10

theorem Equation1654_termStructuralFrom_Equation556 :
    Law1654.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1654.models_iff]
    exact fun x y ↦ @aux556_1654 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 1682 `x = (y ◇ x) ◇ ((x ◇ x) ◇ y)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1682 [Magma G] (h : Equation556 G) (x y : G) :
    x = (((((y ◇ x) ◇ x) ◇ x) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y) ◇ y)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y) ◇ y)) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((y ◇ x) ◇ x) ◇ x) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y) ◇ y)) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y) ◇ y)) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y) ◇ y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef34 :
      x ≠ (((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y))) ◇
      (y ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y))) ◇ (y ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y)) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef35 :
      x ≠ (y ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y)) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y))) ◇
      (y ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y))) := by
    first | exact superpose ef9 ef34 | exact superpose ef34 ef9
  have ef55 :
      x ≠ (y ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y)) ◇ ((y ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y)) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ y) ◇ y)))) := by
    first | exact superpose ef9 ef35 | exact superpose ef35 ef9
  have ef75 :
      x ≠ (y ◇ (y ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ y))) ◇ ((y ◇ (y ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ y))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (y ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ y))))) := by
    first | exact superpose ef9 ef55 | exact superpose ef55 ef9
  have ef95 :
      x ≠ (y ◇ (y ◇ (y ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇ ((y ◇ (y ◇ (y ◇ (((x ◇ x) ◇ x) ◇ x)))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (y ◇ (y ◇ (((x ◇ x) ◇ x) ◇ x)))))) := by
    first | exact superpose ef9 ef75 | exact superpose ef75 ef9
  have ef115 :
      x ≠ (y ◇ (y ◇ (y ◇ (x ◇ ((x ◇ x) ◇ x))))) ◇ ((y ◇ (y ◇ (y ◇ (x ◇ ((x ◇ x) ◇ x))))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (y ◇ (y ◇ (x ◇ ((x ◇ x) ◇ x))))))) := by
    first | exact superpose ef9 ef95 | exact superpose ef95 ef9
  have ef135 :
      x ≠ (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇ ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef9 ef115 | exact superpose ef115 ef9
  have ef155 :
      x ≠ (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇ ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef9 ef135 | exact superpose ef135 ef9
  have ef175 :
      x ≠ (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇ ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      ((x ◇ (x ◇ (y ◇ x))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef9 ef155 | exact superpose ef155 ef9
  have ef195 :
      x ≠ (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇ ((y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))) ◇
      ((x ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ x)))))))) := by
    first | exact superpose ef9 ef175 | exact superpose ef175 ef9
  have ef215 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef221 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X1 := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef582 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ X4) = X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) := by
    first | exact superpose ef215 ef221 | exact superpose ef221 ef215
  have ef602 (X0 : G) :
      x ≠ (X0 ◇ (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ X0))) ◇ ((X0 ◇ (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ X0))) ◇
      ((x ◇ (x ◇ (x ◇ y))) ◇ (X0 ◇ (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ X0))))) := by
    first | exact superpose ef215 ef195 | exact superpose ef195 ef215
  have ef608 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) := by
    first | exact superpose ef215 ef221 | exact superpose ef221 ef215
  have ef613 : x ≠ (x ◇ (y ◇ x)) ◇ ((x ◇ (y ◇ x)) ◇ ((x ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (y ◇ x)))) := by
    first | exact superpose ef608 ef602 | exact superpose ef602 ef608
  have ef632 : x ≠ x ◇ (y ◇ (x ◇ (y ◇ x))) := by
    first | exact superpose ef582 ef613 | exact superpose ef613 ef582
  subsumption ef632 ef10

theorem Equation1682_termStructuralFrom_Equation556 :
    Law1682.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1682.models_iff]
    exact fun x y ↦ @aux556_1682 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 1691 `x = (y ◇ x) ◇ ((y ◇ x) ◇ x)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1691 [Magma G] (h : Equation556 G) (x y : G) :
    x = (((((y ◇ x) ◇ x) ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((y ◇ x) ◇ x) ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef26 :
      x ≠ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef30 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef33 :
      x ≠ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ (((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ ((((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef9 ef26 | exact superpose ef26 ef9
  have ef49 :
      x ≠ (x ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇ ((x ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ (x ◇ (((((y ◇ x) ◇ x) ◇ x) ◇ x) ◇ x)))) := by
    first | exact superpose ef9 ef33 | exact superpose ef33 ef9
  have ef65 :
      x ≠ (x ◇ (x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x))) ◇ ((x ◇ (x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ (x ◇ (x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef9 ef49 | exact superpose ef49 ef9
  have ef81 : x ≠ ((y ◇ x) ◇ x) ◇ (((y ◇ x) ◇ x) ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ x) ◇ x))) := by
    first | exact superpose ef30 ef65 | exact superpose ef65 ef30
  have ef97 : x ≠ ((y ◇ x) ◇ x) ◇ (((y ◇ x) ◇ x) ◇ (((y ◇ x) ◇ x) ◇ (((y ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef9 ef81 | exact superpose ef81 ef9
  subsumption ef97 ef10

theorem Equation1691_termStructuralFrom_Equation556 :
    Law1691.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1691.models_iff]
    exact fun x y ↦ @aux556_1691 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 1722 `x = (y ◇ y) ◇ ((x ◇ y) ◇ y)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1722 [Magma G] (h : Equation556 G) (x y : G) :
    x = (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇ y)) ◇
      ((((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇ y)) ◇ ((((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇ y)) ◇
      ((((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇ y)) ◇ ((((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef32 :
      x ≠ ((((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇ y)) ◇
      ((((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇ y)) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef33 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef35 :
      x ≠ ((((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇ (((((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef9 ef32 | exact superpose ef32 ef9
  have ef55 :
      x ≠ (y ◇ (((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y)) ◇ ((y ◇ (((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y)) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (((((x ◇ y) ◇ y) ◇ y) ◇ y) ◇ y)))) := by
    first | exact superpose ef9 ef35 | exact superpose ef35 ef9
  have ef75 :
      x ≠ (y ◇ (y ◇ ((((x ◇ y) ◇ y) ◇ y) ◇ y))) ◇ ((y ◇ (y ◇ ((((x ◇ y) ◇ y) ◇ y) ◇ y))) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (y ◇ ((((x ◇ y) ◇ y) ◇ y) ◇ y))))) := by
    first | exact superpose ef9 ef55 | exact superpose ef55 ef9
  have ef95 : x ≠ ((x ◇ y) ◇ y) ◇ (((x ◇ y) ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ ((x ◇ y) ◇ y))) := by
    first | exact superpose ef33 ef75 | exact superpose ef75 ef33
  have ef115 : x ≠ ((x ◇ y) ◇ y) ◇ (((x ◇ y) ◇ y) ◇ (((x ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef9 ef95 | exact superpose ef95 ef9
  have ef135 : x ≠ ((x ◇ y) ◇ y) ◇ (((x ◇ y) ◇ y) ◇ (((x ◇ y) ◇ y) ◇ (y ◇ ((y ◇ y) ◇ y)))) := by
    first | exact superpose ef9 ef115 | exact superpose ef115 ef9
  have ef155 : x ≠ ((x ◇ y) ◇ y) ◇ (((x ◇ y) ◇ y) ◇ (((x ◇ y) ◇ y) ◇ (y ◇ (y ◇ (y ◇ y))))) := by
    first | exact superpose ef9 ef135 | exact superpose ef135 ef9
  have ef175 : x ≠ (y ◇ (x ◇ y)) ◇ ((y ◇ (x ◇ y)) ◇ ((y ◇ (x ◇ y)) ◇ (y ◇ (y ◇ (y ◇ y))))) := by
    first | exact superpose ef9 ef155 | exact superpose ef155 ef9
  have ef195 : x ≠ (y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ (y ◇ (y ◇ (y ◇ y))))) := by
    first | exact superpose ef9 ef175 | exact superpose ef175 ef9
  have ef221 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef579 (X0 : G) :
      x ≠ (y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ (X0 ◇ (y ◇ (X0 ◇ y))))) := by
    first | exact superpose ef221 ef195 | exact superpose ef195 ef221
  have ef583 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ X4) = X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    first | exact superpose ef221 ef10 | exact superpose ef10 ef221
  have ef619 : x ≠ y ◇ (y ◇ (y ◇ (y ◇ x))) := by
    first | exact superpose ef583 ef579 | exact superpose ef579 ef583
  subsumption ef619 ef10

theorem Equation1722_termStructuralFrom_Equation556 :
    Law1722.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1722.models_iff]
    exact fun x y ↦ @aux556_1722 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 1729 `x = (y ◇ y) ◇ ((y ◇ x) ◇ y)` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1729 [Magma G] (h : Equation556 G) (x y : G) :
    x = (((((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ y)) ◇
      (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ y)) ◇
      (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef28 :
      x ≠ (((((y ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ y)) ◇
      (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ y) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef29 :
      x ≠ (((y ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ y) ◇
      (((((y ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ y)) ◇
      (((y ◇ y) ◇ y) ◇ y)) := by
    first | exact superpose ef9 ef28 | exact superpose ef28 ef9
  have ef43 :
      x ≠ (((y ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇
      ((((y ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ y))) := by
    first | exact superpose ef9 ef29 | exact superpose ef29 ef9
  have ef57 :
      x ≠ (y ◇ ((y ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x))) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇
      ((y ◇ ((y ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x))) ◇ (y ◇ ((y ◇ y) ◇ ((y ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef9 ef43 | exact superpose ef43 ef9
  have ef71 :
      x ≠ (y ◇ ((y ◇ y) ◇ (x ◇ (y ◇ (x ◇ x))))) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇
      ((y ◇ ((y ◇ y) ◇ (x ◇ (y ◇ (x ◇ x))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (y ◇ (x ◇ x))))))) := by
    first | exact superpose ef9 ef57 | exact superpose ef57 ef9
  have ef85 :
      x ≠ (y ◇ ((y ◇ y) ◇ (x ◇ (y ◇ (x ◇ x))))) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇
      ((y ◇ ((y ◇ y) ◇ (x ◇ (y ◇ (x ◇ x))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (y ◇ (x ◇ x))))))) := by
    first | exact superpose ef9 ef71 | exact superpose ef71 ef9
  have ef99 :
      x ≠ (y ◇ ((y ◇ y) ◇ (x ◇ (y ◇ (x ◇ x))))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇
      ((y ◇ ((y ◇ y) ◇ (x ◇ (y ◇ (x ◇ x))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (y ◇ (x ◇ x))))))) := by
    first | exact superpose ef9 ef85 | exact superpose ef85 ef9
  have ef113 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef117 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef119 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X1 := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef461 (X0 : G) :
      x ≠ X0 ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ (X0 ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (y ◇ (x ◇ x))))))) := by
    first | exact superpose ef113 ef99 | exact superpose ef99 ef113
  have ef512 : x ≠ (x ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ y) := by
    first | exact superpose ef119 ef461 | exact superpose ef461 ef119
  have ef523 : x ≠ (x ◇ (y ◇ (x ◇ x))) ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))) := by
    first | exact superpose ef117 ef512 | exact superpose ef512 ef117
  have ef527 : x ≠ (x ◇ (y ◇ (x ◇ x))) ◇ y := by
    first | exact superpose ef5 ef523 | exact superpose ef523 ef5
  have ef531 : x ≠ y ◇ (x ◇ (y ◇ (x ◇ x))) := by
    first | exact superpose ef9 ef527 | exact superpose ef527 ef9
  subsumption ef531 ef5

theorem Equation1729_termStructuralFrom_Equation556 :
    Law1729.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1729.models_iff]
    exact fun x y ↦ @aux556_1729 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 1731 `x = (y ◇ y) ◇ ((y ◇ y) ◇ x)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_1731 [Magma G] (h : Equation556 G) (x y : G) :
    x = (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef28 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef117 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef161 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef28 ef28
  have ef178 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef28 ef10 | exact superpose ef10 ef28
  have ef203 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef117 ef117
  have ef246 :
      x ≠ (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇ (x ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x)) := by
    first | exact superpose ef117 ef6 | exact superpose ef6 ef117
  have ef247 :
      x ≠ ((((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x) ◇
      (((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef178 ef246 | exact superpose ef246 ef178
  have ef255 :
      x ≠ ((((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x)) ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef203 ef247 | exact superpose ef247 ef203
  subsumption ef255 ef161

theorem Equation1731_termStructuralFrom_Equation556 :
    Law1731.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1731.models_iff]
    exact fun x y ↦ @aux556_1731 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 3253 `x ◇ x = x ◇ (x ◇ (x ◇ x))` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3253 [Magma G] (h : Equation556 G) (x : G) :
    ((x ◇ x) ◇ x) ◇ x =
      ((x ◇ (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ x) ◇ x) ◇
      x ≠ ((x ◇ (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef23 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef25 :
      x ◇ ((x ◇ x) ◇
      x) ≠ ((x ◇ (((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef27 :
      x ◇ ((x ◇ x) ◇ x) ≠ (((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇
      (x ◇ ((x ◇ x) ◇ x))) ◇
      ((x ◇ (((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) := by
    first | exact superpose ef9 ef25 | exact superpose ef25 ef9
  have ef39 :
      x ◇ ((x ◇ x) ◇ x) ≠ (((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇
      (x ◇ ((x ◇ x) ◇ x))) ◇
      ((((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇
      (x ◇ (((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x))))) := by
    first | exact superpose ef9 ef27 | exact superpose ef27 ef9
  have ef51 :
      x ◇ ((x ◇ x) ◇ x) ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇
      ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)))))) := by
    first | exact superpose ef9 ef39 | exact superpose ef39 ef9
  have ef63 :
      x ◇ ((x ◇ x) ◇ x) ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇
      ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))))) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))))) ◇
      (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))))))) := by
    first | exact superpose ef9 ef51 | exact superpose ef51 ef9
  have ef75 :
      x ◇ ((x ◇ x) ◇ x) ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x)))) := by
    first | exact superpose ef23 ef63 | exact superpose ef63 ef23
  have ef87 :
      x ◇ ((x ◇ x) ◇ x) ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) ◇
      (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))))) := by
    first | exact superpose ef9 ef75 | exact superpose ef75 ef9
  have ef99 :
      x ◇ ((x ◇ x) ◇ x) ≠ ((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇
      (((x ◇ ((x ◇ x) ◇ x)) ◇ x) ◇ (x ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ x))) := by
    first | exact superpose ef23 ef87 | exact superpose ef87 ef23
  have ef111 :
      x ◇ ((x ◇ x) ◇ x) ≠ (x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇
      ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x))))) := by
    first | exact superpose ef9 ef99 | exact superpose ef99 ef9
  have ef123 :
      x ◇ ((x ◇ x) ◇ x) ≠ (x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ (x ◇ x)) := by
    first | exact superpose ef5 ef111 | exact superpose ef111 ef5
  have ef135 :
      x ◇ ((x ◇ x) ◇ x) ≠ (x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))) := by
    first | exact superpose ef9 ef123 | exact superpose ef123 ef9
  have ef147 : x ◇ ((x ◇ x) ◇ x) ≠ x ◇ ((x ◇ x) ◇ x) := by
    first | exact superpose ef23 ef135 | exact superpose ef135 ef23
  exact absurd rfl ef147

theorem Equation3253_termStructuralFrom_Equation556 :
    Law3253.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3253.models_iff]
    exact fun x ↦ @aux556_3253 G M h x
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 3261 `x ◇ x = x ◇ (y ◇ (y ◇ x))` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3261 [Magma G] (h : Equation556 G) (x y : G) :
    ((x ◇ x) ◇ x) ◇ x =
      ((x ◇ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ x) ◇ x) ◇
      x ≠ ((x ◇ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef24 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef145 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef189 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef24 ef24
  have ef206 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef24 ef10 | exact superpose ef10 ef24
  have ef231 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef145 ef145
  have ef265 :
      ((x ◇ x) ◇ x) ◇
      x ≠ ((x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef145 ef6 | exact superpose ef6 ef145
  have ef287 :
      ((x ◇ x) ◇ x) ◇
      x ≠ ((x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef145 ef265 | exact superpose ef265 ef145
  have ef300 :
      ((x ◇ x) ◇ x) ◇ x ≠ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇
      ((x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef206 ef287 | exact superpose ef287 ef206
  have ef312 :
      ((x ◇ x) ◇ x) ◇ x ≠ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) ◇
      (x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))))) := by
    first | exact superpose ef231 ef300 | exact superpose ef300 ef231
  have ef324 :
      ((x ◇ x) ◇ x) ◇ x ≠ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      (((y ◇ x) ◇ x) ◇ x)) ◇
      (((((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (((y ◇ x) ◇ x) ◇ x)))) ◇
      (x ◇ ((((y ◇ x) ◇ x) ◇ x) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (((y ◇ x) ◇ x) ◇ x)))))) := by
    first | exact superpose ef231 ef312 | exact superpose ef312 ef231
  have ef336 :
      ((x ◇ x) ◇ x) ◇
      x ≠ (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      (x ◇ (x ◇ x)) := by
    first | exact superpose ef189 ef324 | exact superpose ef324 ef189
  have ef348 :
      ((x ◇ x) ◇ x) ◇ x ≠ ((x ◇ x) ◇ x) ◇
      (((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef206 ef336 | exact superpose ef336 ef206
  have ef360 :
      ((x ◇ x) ◇ x) ◇ x ≠ ((x ◇ x) ◇ x) ◇
      ((x ◇ ((y ◇ x) ◇ x)) ◇ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef231 ef348 | exact superpose ef348 ef231
  have ef372 :
      ((x ◇ x) ◇ x) ◇ x ≠ ((x ◇ x) ◇ x) ◇
      ((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (((y ◇ x) ◇ x) ◇ x)))) := by
    first | exact superpose ef231 ef360 | exact superpose ef360 ef231
  have ef384 :
      ((x ◇ x) ◇ x) ◇ x ≠ ((x ◇ x) ◇ x) ◇
      ((x ◇ ((y ◇ x) ◇ x)) ◇ ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (x ◇ ((y ◇ x) ◇ x))))) := by
    first | exact superpose ef145 ef372 | exact superpose ef372 ef145
  have ef396 : ((x ◇ x) ◇ x) ◇ x ≠ ((x ◇ x) ◇ x) ◇ x := by
    first | exact superpose ef189 ef384 | exact superpose ef384 ef189
  exact absurd rfl ef396

theorem Equation3261_termStructuralFrom_Equation556 :
    Law3261.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3261.models_iff]
    exact fun x y ↦ @aux556_3261 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 3278 `x ◇ x = y ◇ (y ◇ (x ◇ x))` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3278 [Magma G] (h : Equation556 G) (x y : G) :
    ((x ◇ x) ◇ x) ◇ x =
      ((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ x) ◇ x) ◇
      x ≠ ((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef23 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef91 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef135 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef23 ef23
  have ef152 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef23 ef10 | exact superpose ef10 ef23
  have ef177 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef91 ef91
  have ef213 :
      ((x ◇ x) ◇ x) ◇
      x ≠ ((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      ((((x ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef91 ef6 | exact superpose ef6 ef91
  have ef231 :
      ((x ◇ x) ◇ x) ◇ x ≠ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇
      ((y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef152 ef213 | exact superpose ef213 ef152
  have ef244 :
      ((x ◇ x) ◇ x) ◇ x ≠ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ x) ◇ x)) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (y ◇ (((y ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)))) := by
    first | exact superpose ef177 ef231 | exact superpose ef231 ef177
  subsumption ef244 ef135

theorem Equation3278_termStructuralFrom_Equation556 :
    Law3278.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3278.models_iff]
    exact fun x y ↦ @aux556_3278 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 3306 `x ◇ y = x ◇ (x ◇ (x ◇ y))` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3306 [Magma G] (h : Equation556 G) (x y : G) :
    ((x ◇ y) ◇ y) ◇ y =
      ((x ◇ (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ y) ◇ y) ◇
      y ≠ ((x ◇ (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef24 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef117 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef161 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef24 ef24
  have ef178 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef24 ef10 | exact superpose ef10 ef24
  have ef203 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef117 ef117
  have ef239 :
      ((x ◇ y) ◇ y) ◇
      y ≠ ((x ◇ (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      ((((x ◇ y) ◇ y) ◇ y) ◇ ((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef117 ef6 | exact superpose ef6 ef117
  have ef257 :
      ((x ◇ y) ◇ y) ◇ y ≠ (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇
      (((x ◇ y) ◇ y) ◇ y)) ◇
      ((x ◇ (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef178 ef239 | exact superpose ef239 ef178
  have ef270 :
      ((x ◇ y) ◇ y) ◇ y ≠ (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇
      (((x ◇ y) ◇ y) ◇ y)) ◇
      (((((x ◇ y) ◇ y) ◇ y) ◇ ((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (x ◇ (((x ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)))) := by
    first | exact superpose ef203 ef257 | exact superpose ef257 ef203
  subsumption ef270 ef161

theorem Equation3306_termStructuralFrom_Equation556 :
    Law3306.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3306.models_iff]
    exact fun x y ↦ @aux556_3306 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 3319 `x ◇ y = x ◇ (y ◇ (y ◇ y))` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3319 [Magma G] (h : Equation556 G) (x y : G) :
    ((x ◇ y) ◇ y) ◇ y =
      ((x ◇ (((y ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((y ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((y ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ y) ◇ y) ◇
      y ≠ ((x ◇ (((y ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((y ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((y ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y)) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef23 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef25 :
      ((x ◇ y) ◇ y) ◇
      y ≠ ((x ◇ (((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇
      (((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇
      (((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef27 :
      ((x ◇ y) ◇ y) ◇ y ≠ (((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇
      (y ◇ ((y ◇ y) ◇ y))) ◇
      ((x ◇ (((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇
      (((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y)))) := by
    first | exact superpose ef9 ef25 | exact superpose ef25 ef9
  have ef39 :
      ((x ◇ y) ◇ y) ◇ y ≠ (((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇
      (y ◇ ((y ◇ y) ◇ y))) ◇
      ((((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇
      (x ◇ (((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y))))) := by
    first | exact superpose ef9 ef27 | exact superpose ef27 ef9
  have ef51 :
      ((x ◇ y) ◇ y) ◇ y ≠ ((y ◇ ((y ◇ y) ◇ y)) ◇
      ((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇
      (((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇
      (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ y)))))) := by
    first | exact superpose ef9 ef39 | exact superpose ef39 ef9
  have ef63 :
      ((x ◇ y) ◇ y) ◇ y ≠ ((y ◇ ((y ◇ y) ◇ y)) ◇
      ((y ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y))))) ◇
      (((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y))))) ◇
      (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y))))))) := by
    first | exact superpose ef9 ef51 | exact superpose ef51 ef9
  have ef75 :
      ((x ◇ y) ◇ y) ◇ y ≠ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ y)) ◇
      (((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ y)) ◇
      (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ y)))) := by
    first | exact superpose ef23 ef63 | exact superpose ef63 ef23
  have ef87 :
      ((x ◇ y) ◇ y) ◇ y ≠ ((y ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇
      (((y ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y)))) ◇
      (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y)))))) := by
    first | exact superpose ef9 ef75 | exact superpose ef75 ef9
  have ef99 :
      ((x ◇ y) ◇ y) ◇ y ≠ ((y ◇ ((y ◇ y) ◇ y)) ◇ y) ◇
      (((y ◇ ((y ◇ y) ◇ y)) ◇ y) ◇ (x ◇ ((y ◇ ((y ◇ y) ◇ y)) ◇ y))) := by
    first | exact superpose ef23 ef87 | exact superpose ef87 ef23
  have ef111 :
      ((x ◇ y) ◇ y) ◇ y ≠ (y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇
      ((y ◇ (y ◇ ((y ◇ y) ◇ y))) ◇ (x ◇ (y ◇ (y ◇ ((y ◇ y) ◇ y))))) := by
    first | exact superpose ef9 ef99 | exact superpose ef99 ef9
  have ef123 : ((x ◇ y) ◇ y) ◇ y ≠ y ◇ (y ◇ (x ◇ y)) := by
    first | exact superpose ef23 ef111 | exact superpose ef111 ef23
  have ef135 : ((y ◇ x) ◇ y) ◇ y ≠ y ◇ (y ◇ (y ◇ x)) := by
    first | exact superpose ef9 ef123 | exact superpose ef123 ef9
  have ef147 : y ◇ (y ◇ (y ◇ x)) ≠ y ◇ ((y ◇ x) ◇ y) := by
    first | exact superpose ef9 ef135 | exact superpose ef135 ef9
  have ef159 : y ◇ (y ◇ (y ◇ x)) ≠ y ◇ (y ◇ (y ◇ x)) := by
    first | exact superpose ef9 ef147 | exact superpose ef147 ef9
  exact absurd rfl ef159

theorem Equation3319_termStructuralFrom_Equation556 :
    Law3319.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3319.models_iff]
    exact fun x y ↦ @aux556_3319 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 3334 `x ◇ y = x ◇ (z ◇ (z ◇ y))` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3334 [Magma G] (h : Equation556 G) (x y z : G) :
    ((x ◇ y) ◇ y) ◇ y =
      ((x ◇ (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y))) ◇
      (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y))) ◇
      (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ y) ◇ y) ◇
      y ≠ ((x ◇ (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y))) ◇
      (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y))) ◇
      (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef24 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef159 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef203 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef24 ef24
  have ef220 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef24 ef10 | exact superpose ef10 ef24
  have ef245 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef159 ef159
  have ef279 :
      ((x ◇ y) ◇ y) ◇
      y ≠ ((x ◇ ((((z ◇ y) ◇ y) ◇ y) ◇ ((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)))) ◇
      (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y))) ◇
      (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) := by
    first | exact superpose ef159 ef6 | exact superpose ef6 ef159
  have ef301 :
      ((x ◇ y) ◇ y) ◇
      y ≠ ((x ◇ ((((z ◇ y) ◇ y) ◇ y) ◇ ((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)))) ◇
      (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y))) ◇
      ((((z ◇ y) ◇ y) ◇ y) ◇ ((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef159 ef279 | exact superpose ef279 ef159
  have ef314 :
      ((x ◇ y) ◇ y) ◇ y ≠ (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇
      (((z ◇ y) ◇ y) ◇ y)) ◇
      ((x ◇ ((((z ◇ y) ◇ y) ◇ y) ◇ ((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)))) ◇
      (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef220 ef301 | exact superpose ef301 ef220
  have ef326 :
      ((x ◇ y) ◇ y) ◇ y ≠ (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇
      (((z ◇ y) ◇ y) ◇ y)) ◇
      (((((z ◇ y) ◇ y) ◇ y) ◇ ((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y))) ◇
      (x ◇ ((((z ◇ y) ◇ y) ◇ y) ◇ ((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y))))) := by
    first | exact superpose ef245 ef314 | exact superpose ef314 ef245
  have ef338 :
      ((x ◇ y) ◇ y) ◇ y ≠ (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇
      (((z ◇ y) ◇ y) ◇ y)) ◇
      (((((z ◇ y) ◇ y) ◇ y) ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ (z ◇ (((z ◇ y) ◇ y) ◇ y)))) ◇
      (x ◇ ((((z ◇ y) ◇ y) ◇ y) ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ (z ◇ (((z ◇ y) ◇ y) ◇ y)))))) := by
    first | exact superpose ef245 ef326 | exact superpose ef326 ef245
  have ef350 :
      ((x ◇ y) ◇ y) ◇
      y ≠ (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇
      (y ◇ (x ◇ y)) := by
    first | exact superpose ef203 ef338 | exact superpose ef338 ef203
  have ef362 :
      ((x ◇ y) ◇ y) ◇ y ≠ ((x ◇ y) ◇ y) ◇
      (((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y)) := by
    first | exact superpose ef220 ef350 | exact superpose ef350 ef220
  have ef374 :
      ((x ◇ y) ◇ y) ◇ y ≠ ((x ◇ y) ◇ y) ◇
      ((y ◇ ((z ◇ y) ◇ y)) ◇ ((z ◇ (((z ◇ y) ◇ y) ◇ y)) ◇ (((z ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef245 ef362 | exact superpose ef362 ef245
  have ef386 :
      ((x ◇ y) ◇ y) ◇ y ≠ ((x ◇ y) ◇ y) ◇
      ((y ◇ ((z ◇ y) ◇ y)) ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ (z ◇ (((z ◇ y) ◇ y) ◇ y)))) := by
    first | exact superpose ef245 ef374 | exact superpose ef374 ef245
  have ef398 :
      ((x ◇ y) ◇ y) ◇ y ≠ ((x ◇ y) ◇ y) ◇
      ((y ◇ ((z ◇ y) ◇ y)) ◇ ((y ◇ ((z ◇ y) ◇ y)) ◇ (z ◇ (y ◇ ((z ◇ y) ◇ y))))) := by
    first | exact superpose ef159 ef386 | exact superpose ef386 ef159
  have ef410 : ((x ◇ y) ◇ y) ◇ y ≠ ((x ◇ y) ◇ y) ◇ y := by
    first | exact superpose ef203 ef398 | exact superpose ef398 ef203
  exact absurd rfl ef410

theorem Equation3334_termStructuralFrom_Equation556 :
    Law3334.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3334.models_iff]
    exact fun x y z ↦ @aux556_3334 G M h x y z
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 3353 `x ◇ y = y ◇ (y ◇ (x ◇ y))` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3353 [Magma G] (h : Equation556 G) (x y : G) :
    ((x ◇ y) ◇ y) ◇ y =
      ((y ◇ (((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ y) ◇ y) ◇
      y ≠ ((y ◇ (((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef24 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef145 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef189 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef24 ef24
  have ef206 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef24 ef10 | exact superpose ef10 ef24
  have ef231 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef145 ef145
  have ef267 :
      ((x ◇ y) ◇ y) ◇
      y ≠ ((y ◇ (((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      ((((x ◇ y) ◇ y) ◇ y) ◇ ((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef145 ef6 | exact superpose ef6 ef145
  have ef285 :
      ((x ◇ y) ◇ y) ◇ y ≠ (((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇
      (((x ◇ y) ◇ y) ◇ y)) ◇
      ((y ◇ (((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef206 ef267 | exact superpose ef267 ef206
  have ef298 :
      ((x ◇ y) ◇ y) ◇ y ≠ (((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇
      (((x ◇ y) ◇ y) ◇ y)) ◇
      (((((x ◇ y) ◇ y) ◇ y) ◇ ((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (y ◇ (((y ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)))) := by
    first | exact superpose ef231 ef285 | exact superpose ef285 ef231
  subsumption ef298 ef189

theorem Equation3353_termStructuralFrom_Equation556 :
    Law3353.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3353.models_iff]
    exact fun x y ↦ @aux556_3353 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 3414 `x ◇ y = z ◇ (z ◇ (x ◇ y))` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3414 [Magma G] (h : Equation556 G) (x y z : G) :
    ((x ◇ y) ◇ y) ◇ y =
      ((z ◇ (((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ y) ◇ y) ◇
      y ≠ ((z ◇ (((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef24 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef117 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef161 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef24 ef24
  have ef178 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef24 ef10 | exact superpose ef10 ef24
  have ef203 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef117 ef117
  have ef239 :
      ((x ◇ y) ◇ y) ◇
      y ≠ ((z ◇ (((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      ((((x ◇ y) ◇ y) ◇ y) ◇ ((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef117 ef6 | exact superpose ef6 ef117
  have ef257 :
      ((x ◇ y) ◇ y) ◇ y ≠ (((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇
      (((x ◇ y) ◇ y) ◇ y)) ◇
      ((z ◇ (((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef178 ef239 | exact superpose ef239 ef178
  have ef270 :
      ((x ◇ y) ◇ y) ◇ y ≠ (((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇
      (((x ◇ y) ◇ y) ◇ y)) ◇
      (((((x ◇ y) ◇ y) ◇ y) ◇ ((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y))) ◇
      (z ◇ (((z ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)) ◇ (((x ◇ y) ◇ y) ◇ y)))) := by
    first | exact superpose ef203 ef257 | exact superpose ef257 ef203
  subsumption ef270 ef161

theorem Equation3414_termStructuralFrom_Equation556 :
    Law3414.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3414.models_iff]
    exact fun x y z ↦ @aux556_3414 G M h x y z
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 3456 `x ◇ x = x ◇ ((x ◇ x) ◇ x)` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3456 [Magma G] (h : Equation556 G) (x : G) :
    ((x ◇ x) ◇ x) ◇ x =
      (((((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ x)) ◇ x) ◇
      (((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ x) ◇ x) ◇
      x ≠ (((((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ x)) ◇ x) ◇
      (((x ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ x) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef24 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef71 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef101 (X0 X1 X2 X3 : G) : X1 ◇ ((X1 ◇ X2) ◇ X0) = X3 ◇ (X0 ◇ (X2 ◇ X3)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef132 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef24 ef10 | exact superpose ef10 ef24
  have ef183 :
      ((x ◇ x) ◇ x) ◇
      x ≠ (((((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x)) ◇ x) ◇
      (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x) := by
    first | exact superpose ef71 ef6 | exact superpose ef6 ef71
  have ef202 :
      ((x ◇ x) ◇ x) ◇
      x ≠ (((((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x)) ◇ x) ◇
      (x ◇ ((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)))) := by
    first | exact superpose ef71 ef183 | exact superpose ef183 ef71
  have ef209 :
      ((x ◇ x) ◇ x) ◇ x ≠ (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x) ◇
      (((((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x)) ◇ x) := by
    first | exact superpose ef132 ef202 | exact superpose ef202 ef132
  have ef215 :
      ((x ◇ x) ◇ x) ◇ x ≠ (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x) ◇
      (x ◇ ((((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x))) := by
    first | exact superpose ef71 ef209 | exact superpose ef209 ef71
  have ef221 : ((x ◇ x) ◇ x) ◇ x ≠ (x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef5 ef215 | exact superpose ef215 ef5
  have ef227 : ((x ◇ x) ◇ x) ◇ x ≠ (x ◇ x) ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef71 ef221 | exact superpose ef221 ef71
  have ef233 : x ◇ ((x ◇ x) ◇ x) ≠ (x ◇ x) ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef9 ef227 | exact superpose ef227 ef9
  subsumption ef233 ef101

theorem Equation3456_termStructuralFrom_Equation556 :
    Law3456.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3456.models_iff]
    exact fun x ↦ @aux556_3456 G M h x
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 3459 `x ◇ x = x ◇ ((x ◇ y) ◇ y)` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3459 [Magma G] (h : Equation556 G) (x y : G) :
    ((x ◇ x) ◇ x) ◇ x =
      (((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ y)) ◇ x) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ x) ◇ x) ◇
      x ≠ (((((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ y)) ◇ x) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ y) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef22 :
      ((x ◇ x) ◇ x) ◇
      x ≠ (((((y ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ (((y ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ y)) ◇ x) ◇
      (((y ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ y) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef24 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef25 :
      ((x ◇ x) ◇ x) ◇ x ≠ (((y ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ y) ◇
      (((((y ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ (((y ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ y)) ◇ x) := by
    first | exact superpose ef9 ef22 | exact superpose ef22 ef9
  have ef35 :
      ((x ◇ x) ◇ x) ◇ x ≠ (((y ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ y) ◇
      (x ◇ ((((y ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ (((y ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ y))) := by
    first | exact superpose ef9 ef25 | exact superpose ef25 ef9
  have ef45 :
      ((x ◇ x) ◇ x) ◇ x ≠ (y ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y))) ◇
      (x ◇ ((y ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y))))) := by
    first | exact superpose ef9 ef35 | exact superpose ef35 ef9
  have ef55 : ((x ◇ x) ◇ x) ◇ x ≠ x ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef24 ef45 | exact superpose ef45 ef24
  have ef65 : x ◇ (x ◇ (x ◇ x)) ≠ x ◇ ((x ◇ x) ◇ x) := by
    first | exact superpose ef9 ef55 | exact superpose ef55 ef9
  have ef75 : x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef9 ef65 | exact superpose ef65 ef9
  exact absurd rfl ef75

theorem Equation3459_termStructuralFrom_Equation556 :
    Law3459.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3459.models_iff]
    exact fun x y ↦ @aux556_3459 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 3474 `x ◇ x = y ◇ ((x ◇ y) ◇ x)` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3474 [Magma G] (h : Equation556 G) (x y : G) :
    ((x ◇ x) ◇ x) ◇ x =
      (((((x ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((x ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇ y) ◇
      (((x ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ x) ◇ x) ◇
      x ≠ (((((x ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((x ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x)) ◇ y) ◇
      (((x ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef24 :
      ((x ◇ x) ◇ x) ◇
      x ≠ (((((x ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x)) ◇ y) ◇
      (((x ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef25 :
      ((x ◇ x) ◇ x) ◇ x ≠ (((x ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇
      (((((x ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x)) ◇ y) := by
    first | exact superpose ef9 ef24 | exact superpose ef24 ef9
  have ef35 :
      ((x ◇ x) ◇ x) ◇ x ≠ (((x ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇
      (y ◇ ((((x ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ (((x ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x))) := by
    first | exact superpose ef9 ef25 | exact superpose ef25 ef9
  have ef45 :
      ((x ◇ x) ◇ x) ◇ x ≠ (x ◇ ((x ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y))) ◇
      (y ◇ ((x ◇ ((x ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y))) ◇ (x ◇ ((x ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ y))))) := by
    first | exact superpose ef9 ef35 | exact superpose ef35 ef9
  have ef55 :
      ((x ◇ x) ◇ x) ◇ x ≠ (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇ (y ◇ y))))) ◇
      (y ◇ ((x ◇ ((x ◇ x) ◇ (y ◇ (x ◇ (y ◇ y))))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇ (y ◇ y))))))) := by
    first | exact superpose ef9 ef45 | exact superpose ef45 ef9
  have ef65 :
      (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇ (y ◇ y))))) ◇
      (y ◇ ((x ◇ ((x ◇ x) ◇ (y ◇ (x ◇ (y ◇ y))))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇ (y ◇ y))))))) ≠ x ◇
      ((x ◇ x) ◇ x) := by
    first | exact superpose ef9 ef55 | exact superpose ef55 ef9
  have ef75 :
      (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇ (y ◇ y))))) ◇
      (y ◇ ((x ◇ ((x ◇ x) ◇ (y ◇ (x ◇ (y ◇ y))))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇ (y ◇ y))))))) ≠ x ◇
      (x ◇ (x ◇ x)) := by
    first | exact superpose ef9 ef65 | exact superpose ef65 ef9
  have ef85 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef91 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X1 := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef346 (X0 X1 X2 X3 X4 : G) :
      X4 ◇ (X3 ◇ (X4 ◇ X1)) = (X3 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))) := superpose ef85 ef85
  have ef417 (X0 : G) :
      x ◇ (x ◇ (x ◇ x)) ≠ X0 ◇ (y ◇ (X0 ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇ (y ◇ y))))))) := by
    first | exact superpose ef85 ef75 | exact superpose ef75 ef85
  have ef439 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) := by
    first | exact superpose ef85 ef91 | exact superpose ef91 ef85
  have ef465 (X0 : G) :
      x ◇ (x ◇ (x ◇ x)) ≠ (x ◇ x) ◇ (y ◇ (X0 ◇ (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ X0)))) := by
    first | exact superpose ef85 ef417 | exact superpose ef417 ef85
  have ef474 : x ◇ (x ◇ (x ◇ x)) ≠ (x ◇ x) ◇ (y ◇ (x ◇ (x ◇ y))) := by
    first | exact superpose ef439 ef465 | exact superpose ef465 ef439
  subsumption ef474 ef346

theorem Equation3474_termStructuralFrom_Equation556 :
    Law3474.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3474.models_iff]
    exact fun x y ↦ @aux556_3474 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 3518 `x ◇ y = x ◇ ((y ◇ x) ◇ x)` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3518 [Magma G] (h : Equation556 G) (x y : G) :
    ((y ◇ y) ◇ x) ◇ y =
      (((((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x)) ◇ x) ◇
      (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((y ◇ y) ◇ x) ◇
      y ≠ (((((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x)) ◇ x) ◇
      (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X1 ◇ X0)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef24 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef91 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef121 (X0 X1 X2 X3 : G) : X1 ◇ ((X1 ◇ X2) ◇ X0) = X3 ◇ (X0 ◇ (X2 ◇ X3)) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef152 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef24 ef10 | exact superpose ef10 ef24
  have ef218 :
      ((y ◇ y) ◇ x) ◇
      y ≠ (((((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ x) ◇
      (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ y))) ◇ x) := by
    first | exact superpose ef91 ef6 | exact superpose ef6 ef91
  have ef221 :
      ((y ◇ y) ◇ x) ◇
      y ≠ (((((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ x) ◇
      (x ◇ ((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ y)))) := by
    first | exact superpose ef91 ef218 | exact superpose ef218 ef91
  have ef229 :
      ((y ◇ y) ◇ x) ◇ y ≠ (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ y))) ◇ x) ◇
      (((((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ y))) ◇ x)) ◇ x) := by
    first | exact superpose ef152 ef221 | exact superpose ef221 ef152
  have ef235 :
      ((y ◇ y) ◇ x) ◇ y ≠ (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ y))) ◇ x) ◇
      (x ◇ ((((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ y))) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ y))) ◇ x))) := by
    first | exact superpose ef91 ef229 | exact superpose ef229 ef91
  have ef241 : ((y ◇ y) ◇ x) ◇ y ≠ (x ◇ x) ◇ (x ◇ ((x ◇ x) ◇ y)) := by
    first | exact superpose ef5 ef235 | exact superpose ef235 ef5
  have ef247 : ((y ◇ y) ◇ x) ◇ y ≠ (x ◇ x) ◇ (x ◇ (y ◇ (x ◇ x))) := by
    first | exact superpose ef91 ef241 | exact superpose ef241 ef91
  have ef253 : (x ◇ x) ◇ (x ◇ (y ◇ (x ◇ x))) ≠ y ◇ ((y ◇ y) ◇ x) := by
    first | exact superpose ef9 ef247 | exact superpose ef247 ef9
  subsumption ef253 ef121

theorem Equation3518_termStructuralFrom_Equation556 :
    Law3518.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3518.models_iff]
    exact fun x y ↦ @aux556_3518 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 3522 `x ◇ y = x ◇ ((y ◇ y) ◇ y)` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3522 [Magma G] (h : Equation556 G) (x y : G) :
    ((y ◇ y) ◇ x) ◇ y =
      (((((y ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ y)) ◇ x) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((y ◇ y) ◇ x) ◇
      y ≠ (((((y ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ y)) ◇ x) ◇
      (((y ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ y) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef22 :
      ((y ◇ y) ◇ x) ◇
      y ≠ (((((y ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y)) ◇ x) ◇
      (((y ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef24 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef25 :
      ((y ◇ y) ◇ x) ◇ y ≠ (((y ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇
      (((((y ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y)) ◇ x) := by
    first | exact superpose ef9 ef22 | exact superpose ef22 ef9
  have ef35 :
      ((y ◇ y) ◇ x) ◇ y ≠ (((y ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇
      (x ◇ ((((y ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ (((y ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) := by
    first | exact superpose ef9 ef25 | exact superpose ef25 ef9
  have ef45 :
      ((y ◇ y) ◇ x) ◇ y ≠ (y ◇ ((y ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y))) ◇
      (x ◇ ((y ◇ ((y ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ ((y ◇ (y ◇ y)) ◇ y))))) := by
    first | exact superpose ef9 ef35 | exact superpose ef35 ef9
  have ef55 : ((y ◇ y) ◇ x) ◇ y ≠ y ◇ (x ◇ (y ◇ y)) := by
    first | exact superpose ef24 ef45 | exact superpose ef45 ef24
  have ef65 : y ◇ (x ◇ (y ◇ y)) ≠ y ◇ ((y ◇ y) ◇ x) := by
    first | exact superpose ef9 ef55 | exact superpose ef55 ef9
  have ef75 : y ◇ (x ◇ (y ◇ y)) ≠ y ◇ (x ◇ (y ◇ y)) := by
    first | exact superpose ef9 ef65 | exact superpose ef65 ef9
  exact absurd rfl ef75

theorem Equation3522_termStructuralFrom_Equation556 :
    Law3522.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3522.models_iff]
    exact fun x y ↦ @aux556_3522 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 3526 `x ◇ y = x ◇ ((y ◇ z) ◇ z)` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3526 [Magma G] (h : Equation556 G) (x y z : G) :
    ((y ◇ y) ◇ x) ◇ y =
      (((((z ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ z) ◇ (((z ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ z)) ◇ x) ◇
      (((z ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ z) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((y ◇ y) ◇ x) ◇
      y ≠ (((((z ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ z) ◇ (((z ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ z)) ◇ x) ◇
      (((z ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ z) := mod_symm nh
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef22 :
      ((y ◇ y) ◇ x) ◇
      y ≠ (((((z ◇ z) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ z) ◇ (((z ◇ z) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ z)) ◇ x) ◇
      (((z ◇ z) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ z) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef24 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef25 :
      ((y ◇ y) ◇ x) ◇ y ≠ (((z ◇ z) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ z) ◇
      (((((z ◇ z) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ z) ◇ (((z ◇ z) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ z)) ◇ x) := by
    first | exact superpose ef9 ef22 | exact superpose ef22 ef9
  have ef35 :
      ((y ◇ y) ◇ x) ◇ y ≠ (((z ◇ z) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ z) ◇
      (x ◇ ((((z ◇ z) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ z) ◇ (((z ◇ z) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ z))) := by
    first | exact superpose ef9 ef25 | exact superpose ef25 ef9
  have ef45 :
      ((y ◇ y) ◇ x) ◇ y ≠ (z ◇ ((z ◇ z) ◇ ((y ◇ (z ◇ z)) ◇ z))) ◇
      (x ◇ ((z ◇ ((z ◇ z) ◇ ((y ◇ (z ◇ z)) ◇ z))) ◇ (z ◇ ((z ◇ z) ◇ ((y ◇ (z ◇ z)) ◇ z))))) := by
    first | exact superpose ef9 ef35 | exact superpose ef35 ef9
  have ef55 : ((y ◇ y) ◇ x) ◇ y ≠ y ◇ (x ◇ (y ◇ y)) := by
    first | exact superpose ef24 ef45 | exact superpose ef45 ef24
  have ef65 : y ◇ (x ◇ (y ◇ y)) ≠ y ◇ ((y ◇ y) ◇ x) := by
    first | exact superpose ef9 ef55 | exact superpose ef55 ef9
  have ef75 : y ◇ (x ◇ (y ◇ y)) ≠ y ◇ (x ◇ (y ◇ y)) := by
    first | exact superpose ef9 ef65 | exact superpose ef65 ef9
  exact absurd rfl ef75

theorem Equation3526_termStructuralFrom_Equation556 :
    Law3526.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3526.models_iff]
    exact fun x y z ↦ @aux556_3526 G M h x y z
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 3558 `x ◇ y = y ◇ ((y ◇ y) ◇ x)` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3558 [Magma G] (h : Equation556 G) (x y : G) :
    ((y ◇ y) ◇ x) ◇ y =
      (((((x ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((x ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇ y) ◇
      (((x ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((y ◇ y) ◇ x) ◇
      y ≠ (((((x ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ (((x ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇ y) ◇
      (((x ◇ x) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef24 :
      ((y ◇ y) ◇ x) ◇
      y ≠ (((((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ (((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x)) ◇ y) ◇
      (((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef25 :
      ((y ◇ y) ◇ x) ◇ y ≠ (((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇
      (((((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ (((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x)) ◇ y) := by
    first | exact superpose ef9 ef24 | exact superpose ef24 ef9
  have ef35 :
      ((y ◇ y) ◇ x) ◇ y ≠ (((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇
      (y ◇ ((((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x) ◇ (((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ x))) := by
    first | exact superpose ef9 ef25 | exact superpose ef25 ef9
  have ef45 :
      ((y ◇ y) ◇ x) ◇ y ≠ (x ◇ ((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y))) ◇
      (y ◇ ((x ◇ ((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y))) ◇ (x ◇ ((x ◇ x) ◇ ((y ◇ (y ◇ y)) ◇ y))))) := by
    first | exact superpose ef9 ef35 | exact superpose ef35 ef9
  have ef55 :
      ((y ◇ y) ◇ x) ◇ y ≠ (x ◇ ((x ◇ x) ◇ (y ◇ (y ◇ (y ◇ y))))) ◇
      (y ◇ ((x ◇ ((x ◇ x) ◇ (y ◇ (y ◇ (y ◇ y))))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (y ◇ (y ◇ y))))))) := by
    first | exact superpose ef9 ef45 | exact superpose ef45 ef9
  have ef65 :
      (x ◇ ((x ◇ x) ◇ (y ◇ (y ◇ (y ◇ y))))) ◇
      (y ◇ ((x ◇ ((x ◇ x) ◇ (y ◇ (y ◇ (y ◇ y))))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ y ◇
      ((y ◇ y) ◇ x) := by
    first | exact superpose ef9 ef55 | exact superpose ef55 ef9
  have ef75 :
      (x ◇ ((x ◇ x) ◇ (y ◇ (y ◇ (y ◇ y))))) ◇
      (y ◇ ((x ◇ ((x ◇ x) ◇ (y ◇ (y ◇ (y ◇ y))))) ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (y ◇ (y ◇ y))))))) ≠ y ◇
      (x ◇ (y ◇ y)) := by
    first | exact superpose ef9 ef65 | exact superpose ef65 ef9
  have ef85 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef91 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X1 := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef346 (X0 X1 X2 X3 X4 : G) :
      X4 ◇ (X3 ◇ (X4 ◇ X1)) = (X3 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))) := superpose ef85 ef85
  have ef417 (X0 : G) :
      y ◇ (x ◇ (y ◇ y)) ≠ X0 ◇ (y ◇ (X0 ◇ (x ◇ ((x ◇ x) ◇ (y ◇ (y ◇ (y ◇ y))))))) := by
    first | exact superpose ef85 ef75 | exact superpose ef75 ef85
  have ef439 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) := by
    first | exact superpose ef85 ef91 | exact superpose ef91 ef85
  have ef465 (X0 : G) :
      y ◇ (x ◇ (y ◇ y)) ≠ (x ◇ x) ◇ (y ◇ (X0 ◇ (x ◇ ((y ◇ (y ◇ (y ◇ y))) ◇ X0)))) := by
    first | exact superpose ef85 ef417 | exact superpose ef417 ef85
  have ef474 : y ◇ (x ◇ (y ◇ y)) ≠ (x ◇ x) ◇ (y ◇ (y ◇ (x ◇ y))) := by
    first | exact superpose ef439 ef465 | exact superpose ef465 ef439
  subsumption ef474 ef346

theorem Equation3558_termStructuralFrom_Equation556 :
    Law3558.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3558.models_iff]
    exact fun x y ↦ @aux556_3558 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 3607 `x ◇ y = z ◇ ((y ◇ z) ◇ x)` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_3607 [Magma G] (h : Equation556 G) (x y z : G) :
    ((y ◇ y) ◇ x) ◇ y =
      (((((x ◇ x) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ x) ◇ (((x ◇ x) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ x)) ◇ z) ◇
      (((x ◇ x) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((y ◇ y) ◇ x) ◇
      y ≠ (((((x ◇ x) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ x) ◇ (((x ◇ x) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ x)) ◇ z) ◇
      (((x ◇ x) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef24 :
      ((y ◇ y) ◇ x) ◇
      y ≠ (((((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ x) ◇ (((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ x)) ◇ z) ◇
      (((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ x) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef25 :
      ((y ◇ y) ◇ x) ◇ y ≠ (((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ x) ◇
      (((((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ x) ◇ (((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ x)) ◇ z) := by
    first | exact superpose ef9 ef24 | exact superpose ef24 ef9
  have ef35 :
      ((y ◇ y) ◇ x) ◇ y ≠ (((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ x) ◇
      (z ◇ ((((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ x) ◇ (((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ z)) ◇ x))) := by
    first | exact superpose ef9 ef25 | exact superpose ef25 ef9
  have ef45 :
      ((y ◇ y) ◇ x) ◇ y ≠ (x ◇ ((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ z))) ◇
      (z ◇ ((x ◇ ((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ z))) ◇ (x ◇ ((x ◇ x) ◇ ((y ◇ (z ◇ z)) ◇ z))))) := by
    first | exact superpose ef9 ef35 | exact superpose ef35 ef9
  have ef55 :
      ((y ◇ y) ◇ x) ◇ y ≠ (x ◇ ((x ◇ x) ◇ (z ◇ (y ◇ (z ◇ z))))) ◇
      (z ◇ ((x ◇ ((x ◇ x) ◇ (z ◇ (y ◇ (z ◇ z))))) ◇ (x ◇ ((x ◇ x) ◇ (z ◇ (y ◇ (z ◇ z))))))) := by
    first | exact superpose ef9 ef45 | exact superpose ef45 ef9
  have ef65 :
      (x ◇ ((x ◇ x) ◇ (z ◇ (y ◇ (z ◇ z))))) ◇
      (z ◇ ((x ◇ ((x ◇ x) ◇ (z ◇ (y ◇ (z ◇ z))))) ◇ (x ◇ ((x ◇ x) ◇ (z ◇ (y ◇ (z ◇ z))))))) ≠ y ◇
      ((y ◇ y) ◇ x) := by
    first | exact superpose ef9 ef55 | exact superpose ef55 ef9
  have ef75 :
      (x ◇ ((x ◇ x) ◇ (z ◇ (y ◇ (z ◇ z))))) ◇
      (z ◇ ((x ◇ ((x ◇ x) ◇ (z ◇ (y ◇ (z ◇ z))))) ◇ (x ◇ ((x ◇ x) ◇ (z ◇ (y ◇ (z ◇ z))))))) ≠ y ◇
      (x ◇ (y ◇ y)) := by
    first | exact superpose ef9 ef65 | exact superpose ef65 ef9
  have ef85 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef91 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X1 := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef346 (X0 X1 X2 X3 X4 : G) :
      X4 ◇ (X3 ◇ (X4 ◇ X1)) = (X3 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))) := superpose ef85 ef85
  have ef417 (X0 : G) :
      y ◇ (x ◇ (y ◇ y)) ≠ X0 ◇ (z ◇ (X0 ◇ (x ◇ ((x ◇ x) ◇ (z ◇ (y ◇ (z ◇ z))))))) := by
    first | exact superpose ef85 ef75 | exact superpose ef75 ef85
  have ef439 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) := by
    first | exact superpose ef85 ef91 | exact superpose ef91 ef85
  have ef465 (X0 : G) :
      y ◇ (x ◇ (y ◇ y)) ≠ (x ◇ x) ◇ (z ◇ (X0 ◇ (x ◇ ((z ◇ (y ◇ (z ◇ z))) ◇ X0)))) := by
    first | exact superpose ef85 ef417 | exact superpose ef417 ef85
  have ef474 : y ◇ (x ◇ (y ◇ y)) ≠ (x ◇ x) ◇ (z ◇ (y ◇ (x ◇ z))) := by
    first | exact superpose ef439 ef465 | exact superpose ef465 ef439
  subsumption ef474 ef346

theorem Equation3607_termStructuralFrom_Equation556 :
    Law3607.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law3607.models_iff]
    exact fun x y z ↦ @aux556_3607 G M h x y z
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 4275 `x ◇ (x ◇ x) = y ◇ (y ◇ x)` holds of the term `x □ y := ((x ◇ y) ◇ y) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_4275 [Magma G] (h : Equation556 G) (x y : G) :
    ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x) =
      ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ x) ◇ x) ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      (((y ◇ x) ◇ x) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef20 (X0 X1 X2 : G) : X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := by
    first | exact superpose ef9 ef5 | exact superpose ef5 ef9
  have ef149 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef193 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ X1)) = X3 := superpose ef20 ef20
  have ef210 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = (X0 ◇ X2) ◇ X1 := by
    first | exact superpose ef20 ef10 | exact superpose ef10 ef20
  have ef235 (X0 X1 X2 X3 : G) :
      X3 ◇ ((X2 ◇ X1) ◇ X0) = X3 ◇ (X0 ◇ (X1 ◇ X2)) := superpose ef149 ef149
  have ef268 :
      ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ x) ◇ x) ≠ ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) ◇
      (x ◇ ((y ◇ x) ◇ x)) := by
    first | exact superpose ef149 ef6 | exact superpose ef6 ef149
  have ef280 :
      ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ x) ◇ x) ≠ (((y ◇ x) ◇ x) ◇ x) ◇
      ((y ◇ (((y ◇ x) ◇ x) ◇ x)) ◇ (((y ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef210 ef268 | exact superpose ef268 ef210
  have ef287 :
      ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇
      (((x ◇ x) ◇ x) ◇ x) ≠ (((y ◇ x) ◇ x) ◇ x) ◇
      ((x ◇ ((y ◇ x) ◇ x)) ◇ (y ◇ (((y ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef235 ef280 | exact superpose ef280 ef235
  have ef293 : x ≠ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x) := by
    first | exact superpose ef193 ef287 | exact superpose ef287 ef193
  have ef299 : x ≠ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (x ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef149 ef293 | exact superpose ef293 ef149
  have ef305 : x ≠ (((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x)) := by
    first | exact superpose ef210 ef299 | exact superpose ef299 ef210
  have ef311 : x ≠ (((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef235 ef305 | exact superpose ef305 ef235
  subsumption ef311 ef193

theorem Equation4275_termStructuralFrom_Equation556 :
    Law4275.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) y) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law4275.models_iff]
    exact fun x y ↦ @aux556_4275 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 1)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 1) (Term.var 0))), funext fun z ↦ (@inv556_46197021 G M h (z 0) (z 1)).symm⟩

/-- Equation 4290 `x ◇ (x ◇ y) = y ◇ (x ◇ x)` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_4290 [Magma G] (h : Equation556 G) (x y : G) :
    (((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇ (((y ◇ y) ◇ x) ◇ y) =
      (((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      (((((y ◇ y) ◇ x) ◇ y) ◇ (((y ◇ y) ◇ x) ◇ y)) ◇ x) ◇
      (((y ◇ y) ◇ x) ◇ y) ≠ (((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ x) ◇ x) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef20 :
      (((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ x) ◇ x) ◇ x) ≠ ((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) ◇
      ((x ◇ (y ◇ y)) ◇ y) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef23 :
      (((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ x) ◇ x) ◇ x) ≠ ((x ◇ (y ◇ y)) ◇ y) ◇
      ((((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y)) ◇ x) := by
    first | exact superpose ef9 ef20 | exact superpose ef20 ef9
  have ef31 :
      (((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ x) ◇ x) ◇ x) ≠ ((x ◇ (y ◇ y)) ◇ y) ◇
      (x ◇ (((x ◇ (y ◇ y)) ◇ y) ◇ ((x ◇ (y ◇ y)) ◇ y))) := by
    first | exact superpose ef9 ef23 | exact superpose ef23 ef9
  have ef39 :
      (((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y) ◇
      (((x ◇ x) ◇ x) ◇ x) ≠ (y ◇ (x ◇ (y ◇ y))) ◇
      (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y))))) := by
    first | exact superpose ef9 ef31 | exact superpose ef31 ef9
  have ef47 :
      (y ◇ (x ◇ (y ◇ y))) ◇
      (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y))))) ≠ (((x ◇ x) ◇ x) ◇ x) ◇
      (((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y) := by
    first | exact superpose ef9 ef39 | exact superpose ef39 ef9
  have ef55 :
      (y ◇ (x ◇ (y ◇ y))) ◇
      (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y))))) ≠ (((x ◇ x) ◇ x) ◇ x) ◇
      (y ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) := by
    first | exact superpose ef9 ef47 | exact superpose ef47 ef9
  have ef63 :
      (y ◇ (x ◇ (y ◇ y))) ◇
      (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y))))) ≠ (x ◇ ((x ◇ x) ◇ x)) ◇
      (y ◇ ((x ◇ ((x ◇ x) ◇ x)) ◇ (x ◇ ((x ◇ x) ◇ x)))) := by
    first | exact superpose ef9 ef55 | exact superpose ef55 ef9
  have ef71 :
      (y ◇ (x ◇ (y ◇ y))) ◇
      (x ◇ ((y ◇ (x ◇ (y ◇ y))) ◇ (y ◇ (x ◇ (y ◇ y))))) ≠ (x ◇ (x ◇ (x ◇ x))) ◇
      (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef9 ef63 | exact superpose ef63 ef9
  have ef79 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef85 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X1 := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef412 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ X4) = X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) := by
    first | exact superpose ef79 ef85 | exact superpose ef85 ef79
  have ef416 (X0 : G) :
      (x ◇ (x ◇ (x ◇ x))) ◇
      (y ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (x ◇ x))))) ≠ (X0 ◇ (x ◇ (X0 ◇ y))) ◇
      (x ◇ ((X0 ◇ (x ◇ (X0 ◇ y))) ◇ (X0 ◇ (x ◇ (X0 ◇ y))))) := by
    first | exact superpose ef79 ef71 | exact superpose ef71 ef79
  have ef435 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    first | exact superpose ef79 ef10 | exact superpose ef10 ef79
  have ef444 (X0 : G) :
      (X0 ◇ (x ◇ (X0 ◇ y))) ◇ (x ◇ ((X0 ◇ (x ◇ (X0 ◇ y))) ◇ (X0 ◇ (x ◇ (X0 ◇ y))))) ≠ x ◇
      (y ◇ x) := by
    first | exact superpose ef435 ef416 | exact superpose ef416 ef435
  subsumption ef444 ef412

theorem Equation4290_termStructuralFrom_Equation556 :
    Law4290.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law4290.models_iff]
    exact fun x y ↦ @aux556_4290 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- Equation 4369 `x ◇ (y ◇ z) = z ◇ (y ◇ x)` holds of the term `x □ y := ((y ◇ y) ◇ x) ◇ y` over
any magma satisfying equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. -/
private theorem aux556_4369 [Magma G] (h : Equation556 G) (x y z : G) :
    (((((z ◇ z) ◇ y) ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ x) ◇ (((z ◇ z) ◇ y) ◇ z) =
      (((((x ◇ x) ◇ y) ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ z) ◇ (((x ◇ x) ◇ y) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef6 :
      (((((z ◇ z) ◇ y) ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ x) ◇
      (((z ◇ z) ◇ y) ◇ z) ≠ (((((x ◇ x) ◇ y) ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ z) ◇
      (((x ◇ x) ◇ y) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose ef5 ef5
  have ef9 (X0 X1 : G) : X0 ◇ X1 = X1 ◇ X0 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X2 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef20 :
      (((((z ◇ z) ◇ y) ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ x) ◇
      (((z ◇ z) ◇ y) ◇ z) ≠ ((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ z) ◇
      ((y ◇ (x ◇ x)) ◇ x) := by
    first | exact superpose ef9 ef6 | exact superpose ef6 ef9
  have ef23 :
      (((((z ◇ z) ◇ y) ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ x) ◇
      (((z ◇ z) ◇ y) ◇ z) ≠ ((y ◇ (x ◇ x)) ◇ x) ◇
      ((((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x)) ◇ z) := by
    first | exact superpose ef9 ef20 | exact superpose ef20 ef9
  have ef31 :
      (((((z ◇ z) ◇ y) ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ x) ◇
      (((z ◇ z) ◇ y) ◇ z) ≠ ((y ◇ (x ◇ x)) ◇ x) ◇
      (z ◇ (((y ◇ (x ◇ x)) ◇ x) ◇ ((y ◇ (x ◇ x)) ◇ x))) := by
    first | exact superpose ef9 ef23 | exact superpose ef23 ef9
  have ef39 :
      (((((z ◇ z) ◇ y) ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ x) ◇
      (((z ◇ z) ◇ y) ◇ z) ≠ (x ◇ (y ◇ (x ◇ x))) ◇
      (z ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (y ◇ (x ◇ x))))) := by
    first | exact superpose ef9 ef31 | exact superpose ef31 ef9
  have ef47 :
      (x ◇ (y ◇ (x ◇ x))) ◇
      (z ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (y ◇ (x ◇ x))))) ≠ (((z ◇ z) ◇ y) ◇ z) ◇
      (((((z ◇ z) ◇ y) ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z)) ◇ x) := by
    first | exact superpose ef9 ef39 | exact superpose ef39 ef9
  have ef55 :
      (x ◇ (y ◇ (x ◇ x))) ◇
      (z ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (y ◇ (x ◇ x))))) ≠ (((z ◇ z) ◇ y) ◇ z) ◇
      (x ◇ ((((z ◇ z) ◇ y) ◇ z) ◇ (((z ◇ z) ◇ y) ◇ z))) := by
    first | exact superpose ef9 ef47 | exact superpose ef47 ef9
  have ef63 :
      (x ◇ (y ◇ (x ◇ x))) ◇
      (z ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (y ◇ (x ◇ x))))) ≠ (z ◇ ((z ◇ z) ◇ y)) ◇
      (x ◇ ((z ◇ ((z ◇ z) ◇ y)) ◇ (z ◇ ((z ◇ z) ◇ y)))) := by
    first | exact superpose ef9 ef55 | exact superpose ef55 ef9
  have ef71 :
      (x ◇ (y ◇ (x ◇ x))) ◇
      (z ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ (x ◇ (y ◇ (x ◇ x))))) ≠ (z ◇ (y ◇ (z ◇ z))) ◇
      (x ◇ ((z ◇ (y ◇ (z ◇ z))) ◇ (z ◇ (y ◇ (z ◇ z))))) := by
    first | exact superpose ef9 ef63 | exact superpose ef63 ef9
  have ef79 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X3)) = X1 ◇ (X2 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef5 ef10 | exact superpose ef10 ef5
  have ef85 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X1 := by
    first | exact superpose ef9 ef10 | exact superpose ef10 ef9
  have ef412 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X2 ◇ X4) = X3 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) := by
    first | exact superpose ef79 ef85 | exact superpose ef85 ef79
  have ef416 (X0 : G) :
      (z ◇ (y ◇ (z ◇ z))) ◇
      (x ◇ ((z ◇ (y ◇ (z ◇ z))) ◇ (z ◇ (y ◇ (z ◇ z))))) ≠ (X0 ◇ (y ◇ (X0 ◇ x))) ◇
      (z ◇ ((X0 ◇ (y ◇ (X0 ◇ x))) ◇ (X0 ◇ (y ◇ (X0 ◇ x))))) := by
    first | exact superpose ef79 ef71 | exact superpose ef71 ef79
  have ef435 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ (X4 ◇ X2) = X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    first | exact superpose ef79 ef10 | exact superpose ef10 ef79
  have ef444 (X0 : G) :
      (X0 ◇ (y ◇ (X0 ◇ x))) ◇ (z ◇ ((X0 ◇ (y ◇ (X0 ◇ x))) ◇ (X0 ◇ (y ◇ (X0 ◇ x))))) ≠ y ◇
      (x ◇ z) := by
    first | exact superpose ef435 ef416 | exact superpose ef416 ef435
  subsumption ef444 ef412

theorem Equation4369_termStructuralFrom_Equation556 :
    Law4369.TermStructuralFrom Law556 := by
  intro G M hGL
  have h : Equation556 G := Law556.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law4369.models_iff]
    exact fun x y z ↦ @aux556_4369 G M h x y z
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv556_0b95aece G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := (x ◇ x) ◇ y` of equation 690 `x = y ◇ (x ◇ ((z ◇ y) ◇ x))` can be
undone: the operation is recovered as `x ◇ y = (x ◇ (x ◇ x)) ◇ y` read in `□`. -/
private theorem inv690_b17ab2c2 [Magma G] (h : Equation690 G) (x y : G) :
    (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ y = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 : (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ y ≠ x ◇ y := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0) = X1 ◇ ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X0) := superpose ef5 ef5
  have ef11 (X0 X1 X4 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) = X4 := superpose ef7 ef7
  have ef17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)) = X2 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef20 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X1) = (X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef25 (X0 X1 : G) :
      (X0 ◇ (X1 ◇ X0)) ◇ X0 = X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef37 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0 = X4 ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef117 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef11 ef23 | exact superpose ef23 ef11
  have ef118 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X0 ◇ (X2 ◇ X0)) ◇ X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef296 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X2 ◇ (X3 ◇ X0)) ◇ X0 := by
    first | exact superpose ef31 ef17 | exact superpose ef17 ef31
  have ef302 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1) := by
    first | exact superpose ef31 ef5 | exact superpose ef5 ef31
  have ef400 (X0 X1 X2 X3 : G) : X0 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef118 ef23 | exact superpose ef23 ef118
  have ef496 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X2 ◇ X3) ◇ X0) = (X3 ◇ (X4 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef118 ef20 | exact superpose ef20 ef118
  have ef548 (X0 X2 X3 X4 : G) : X0 ◇ ((X4 ◇ X3) ◇ X0) = X0 ◇ ((X2 ◇ X3) ◇ X0) := by
    first | exact superpose ef400 ef496 | exact superpose ef496 ef400
  have ef601 (X0 X1 X2 X3 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇
      (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef17 ef296 | exact superpose ef296 ef17
  have ef700 (X0 X1 X3 : G) : (X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef302 ef601 | exact superpose ef601 ef302
  have ef764 (X0 X1 X2 : G) :
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef25 ef23 | exact superpose ef23 ef25
  have ef788 (X0 X1 X2 : G) :
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef700 ef764 | exact superpose ef764 ef700
  have ef808 (X0 X1 X2 : G) :
      X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef400 ef788 | exact superpose ef788 ef400
  have ef824 (X0 X1 X2 : G) : X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇ (X1 ◇ X0) := by
    first | exact superpose ef7 ef808 | exact superpose ef808 ef7
  have ef1380 (X0 X1 X2 X3 : G) :
      (X1 ◇ X2) ◇ X0 = (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    first | exact superpose ef548 ef7 | exact superpose ef7 ef548
  have ef3392 (X0 X1 X2 X3 : G) :
      (X3 ◇ X2) ◇ X0 = (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    first | exact superpose ef5 ef824 | exact superpose ef824 ef5
  have ef3394 (X0 X1 X2 X3 : G) :
      (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0))) =
      (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0 := by
    first | exact superpose ef11 ef824 | exact superpose ef824 ef11
  have ef3474 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ ((X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X3) = ((X2 ◇ (X1 ◇ X2)) ◇ X2) ◇
      ((X3 ◇ ((X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X3)) ◇ X3) := by
    first | exact superpose ef824 ef8 | exact superpose ef8 ef824
  have ef3681 (X0 X1 X2 X3 X4 : G) :
      X3 ◇ (X2 ◇ X3) = X3 ◇ ((X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X3) := by
    first | exact superpose ef400 ef3474 | exact superpose ef3474 ef400
  have ef3716 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X1)) ◇ X0 = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0 := by
    first | exact superpose ef1380 ef3394 | exact superpose ef3394 ef1380
  have ef3718 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ X0 = (X3 ◇ X2) ◇ X0 := by
    first | exact superpose ef1380 ef3392 | exact superpose ef3392 ef1380
  have ef4662 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) = (X4 ◇ (X3 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef3718 ef824 | exact superpose ef824 ef3718
  have ef4763 (X0 : G) : x ◇ y ≠ (X0 ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ y := by
    first | exact superpose ef3718 ef6 | exact superpose ef6 ef3718
  have ef5069 (X0 X1 X2 X3 X4 : G) :
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) = X4 ◇
      ((((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)))) ◇
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0))) := by
    first | exact superpose ef37 ef25 | exact superpose ef25 ef37
  have ef5151 (X0 X1 X2 X3 X4 : G) :
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) = X4 ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0) ◇ ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0))) := by
    first | exact superpose ef4662 ef5069 | exact superpose ef5069 ef4662
  have ef5233 (X0 X1 X2 X3 X4 : G) :
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) = X4 ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇
      (X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0))) := by
    first | exact superpose ef3681 ef5151 | exact superpose ef5151 ef3681
  have ef5284 (X0 X1 X2 X3 X4 : G) :
      X4 ◇ X0 =
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) := by
    first | exact superpose ef117 ef5233 | exact superpose ef5233 ef117
  have ef5314 (X0 X1 X2 X3 X4 : G) :
      X4 ◇ X0 = (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) := by
    first | exact superpose ef3716 ef5284 | exact superpose ef5284 ef3716
  have ef5326 (X0 X1 X2 X3 X4 : G) : X4 ◇ X0 = (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 := by
    first | exact superpose ef1380 ef5314 | exact superpose ef5314 ef1380
  have ef5339 :
      x ◇ y ≠ (((x ◇ x) ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ x))) ◇ ((x ◇ x) ◇ x))) ◇
      y := by
    first | exact superpose ef824 ef4763 | exact superpose ef4763 ef824
  subsumption ef5339 ef5326

/-- Equation 817 `x = x ◇ ((x ◇ x) ◇ (x ◇ x))` holds of the term `x □ y := (x ◇ x) ◇ y` over any
magma satisfying equation 690 `x = y ◇ (x ◇ ((z ◇ y) ◇ x))`. -/
private theorem aux690_817 [Magma G] (h : Equation690 G) (x : G) :
    x = (x ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 : x ≠ (x ◇ x) ◇ ((((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ ((x ◇ x) ◇ x)) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0) = X1 ◇ ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X0) := superpose ef5 ef5
  have ef11 (X0 X1 X4 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) = X4 := superpose ef7 ef7
  have ef18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)) = X2 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef20 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X1) = (X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef25 (X0 X1 : G) :
      (X0 ◇ (X1 ◇ X0)) ◇ X0 = X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef33 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef123 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef11 ef23 | exact superpose ef23 ef11
  have ef124 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X0 ◇ (X2 ◇ X0)) ◇ X0 := by
    first | exact superpose ef11 ef18 | exact superpose ef18 ef11
  have ef298 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1) := by
    first | exact superpose ef33 ef5 | exact superpose ef5 ef33
  have ef305 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X2 ◇ (X3 ◇ X0)) ◇ X0 := by
    first | exact superpose ef33 ef18 | exact superpose ef18 ef33
  have ef400 (X0 X1 X2 X3 : G) : X0 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef23 | exact superpose ef23 ef124
  have ef496 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X2 ◇ X3) ◇ X0) = (X3 ◇ (X4 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef20 | exact superpose ef20 ef124
  have ef548 (X0 X2 X3 X4 : G) : X0 ◇ ((X4 ◇ X3) ◇ X0) = X0 ◇ ((X2 ◇ X3) ◇ X0) := by
    first | exact superpose ef400 ef496 | exact superpose ef496 ef400
  have ef601 (X0 X1 X2 X3 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇
      (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef18 ef305 | exact superpose ef305 ef18
  have ef700 (X0 X1 X3 : G) : (X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef601 | exact superpose ef601 ef298
  have ef770 (X0 X1 X2 : G) :
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef25 ef23 | exact superpose ef23 ef25
  have ef785 (X0 X1 X2 : G) :
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef700 ef770 | exact superpose ef770 ef700
  have ef806 (X0 X1 X2 : G) :
      X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef400 ef785 | exact superpose ef785 ef400
  have ef822 (X0 X1 X2 : G) : X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇ (X1 ◇ X0) := by
    first | exact superpose ef7 ef806 | exact superpose ef806 ef7
  have ef1359 (X0 X1 X2 : G) : X1 ◇ X0 = (X0 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef548 ef18 | exact superpose ef18 ef548
  have ef3392 (X0 X1 X2 X3 : G) :
      (X3 ◇ X2) ◇ X0 = (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    first | exact superpose ef5 ef822 | exact superpose ef822 ef5
  have ef3717 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ X0 = (X3 ◇ X2) ◇ X0 := by
    first | exact superpose ef1359 ef3392 | exact superpose ef3392 ef1359
  have ef4531 (X0 : G) : x ≠ (x ◇ x) ◇ ((((X0 ◇ x) ◇ x) ◇ ((X0 ◇ x) ◇ x)) ◇ ((X0 ◇ x) ◇ x)) := by
    first | exact superpose ef3717 ef6 | exact superpose ef6 ef3717
  have ef4574 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) = (X4 ◇ (X3 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef3717 ef822 | exact superpose ef822 ef3717
  have ef4648 (X0 : G) : x ≠ (x ◇ x) ◇ (x ◇ ((x ◇ ((X0 ◇ x) ◇ x)) ◇ x)) := by
    first | exact superpose ef4574 ef4531 | exact superpose ef4531 ef4574
  subsumption ef4648 ef123

theorem Equation817_termStructuralFrom_Equation690 :
    Law817.TermStructuralFrom Law690 := by
  intro G M hGL
  have h : Equation690 G := Law690.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law817.models_iff]
    exact fun x ↦ @aux690_817 G M h x
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv690_b17ab2c2 G M h (z 0) (z 1)).symm⟩

/-- Equation 825 `x = x ◇ ((x ◇ y) ◇ (y ◇ x))` holds of the term `x □ y := (x ◇ x) ◇ y` over any
magma satisfying equation 690 `x = y ◇ (x ◇ ((z ◇ y) ◇ x))`. -/
private theorem aux690_825 [Magma G] (h : Equation690 G) (x y : G) :
    x = (x ◇ x) ◇ ((((x ◇ x) ◇ y) ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ y) ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 : x ≠ (x ◇ x) ◇ ((((x ◇ x) ◇ y) ◇ ((x ◇ x) ◇ y)) ◇ ((y ◇ y) ◇ x)) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0) = X1 ◇ ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X0) := superpose ef5 ef5
  have ef11 (X0 X1 X4 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) = X4 := superpose ef7 ef7
  have ef18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)) = X2 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef20 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X1) = (X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef25 (X0 X1 : G) :
      (X0 ◇ (X1 ◇ X0)) ◇ X0 = X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef123 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef11 ef23 | exact superpose ef23 ef11
  have ef124 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X0 ◇ (X2 ◇ X0)) ◇ X0 := by
    first | exact superpose ef11 ef18 | exact superpose ef18 ef11
  have ef298 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1) := by
    first | exact superpose ef31 ef5 | exact superpose ef5 ef31
  have ef305 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X2 ◇ (X3 ◇ X0)) ◇ X0 := by
    first | exact superpose ef31 ef18 | exact superpose ef18 ef31
  have ef400 (X0 X1 X2 X3 : G) : X0 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef23 | exact superpose ef23 ef124
  have ef496 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X2 ◇ X3) ◇ X0) = (X3 ◇ (X4 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef20 | exact superpose ef20 ef124
  have ef548 (X0 X2 X3 X4 : G) : X0 ◇ ((X4 ◇ X3) ◇ X0) = X0 ◇ ((X2 ◇ X3) ◇ X0) := by
    first | exact superpose ef400 ef496 | exact superpose ef496 ef400
  have ef601 (X0 X1 X2 X3 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇
      (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef18 ef305 | exact superpose ef305 ef18
  have ef700 (X0 X1 X3 : G) : (X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef601 | exact superpose ef601 ef298
  have ef764 (X0 X1 X2 : G) :
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef25 ef23 | exact superpose ef23 ef25
  have ef788 (X0 X1 X2 : G) :
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef700 ef764 | exact superpose ef764 ef700
  have ef808 (X0 X1 X2 : G) :
      X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef400 ef788 | exact superpose ef788 ef400
  have ef824 (X0 X1 X2 : G) : X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇ (X1 ◇ X0) := by
    first | exact superpose ef7 ef808 | exact superpose ef808 ef7
  have ef1405 (X0 X1 X2 X3 : G) :
      (X1 ◇ X2) ◇ X0 = (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    first | exact superpose ef548 ef7 | exact superpose ef7 ef548
  have ef3392 (X0 X1 X2 X3 : G) :
      (X3 ◇ X2) ◇ X0 = (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    first | exact superpose ef5 ef824 | exact superpose ef824 ef5
  have ef3718 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ X0 = (X3 ◇ X2) ◇ X0 := by
    first | exact superpose ef1405 ef3392 | exact superpose ef3392 ef1405
  have ef4672 (X0 : G) : x ≠ (x ◇ x) ◇ ((((X0 ◇ x) ◇ y) ◇ ((X0 ◇ x) ◇ y)) ◇ ((y ◇ y) ◇ x)) := by
    first | exact superpose ef3718 ef6 | exact superpose ef6 ef3718
  have ef4716 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) = (X4 ◇ (X3 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef3718 ef824 | exact superpose ef824 ef3718
  have ef4789 : x ≠ (x ◇ x) ◇ (x ◇ ((x ◇ ((y ◇ y) ◇ x)) ◇ x)) := by
    first | exact superpose ef4716 ef4672 | exact superpose ef4672 ef4716
  subsumption ef4789 ef123

theorem Equation825_termStructuralFrom_Equation690 :
    Law825.TermStructuralFrom Law690 := by
  intro G M hGL
  have h : Equation690 G := Law690.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law825.models_iff]
    exact fun x y ↦ @aux690_825 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv690_b17ab2c2 G M h (z 0) (z 1)).symm⟩

/-- Equation 832 `x = x ◇ ((y ◇ x) ◇ (x ◇ x))` holds of the term `x □ y := (x ◇ x) ◇ y` over any
magma satisfying equation 690 `x = y ◇ (x ◇ ((z ◇ y) ◇ x))`. -/
private theorem aux690_832 [Magma G] (h : Equation690 G) (x y : G) :
    x = (x ◇ x) ◇ ((((y ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ x) ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 : x ≠ (x ◇ x) ◇ ((((y ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ ((x ◇ x) ◇ x)) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0) = X1 ◇ ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X0) := superpose ef5 ef5
  have ef11 (X0 X1 X4 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) = X4 := superpose ef7 ef7
  have ef18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)) = X2 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef20 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X1) = (X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef25 (X0 X1 : G) :
      (X0 ◇ (X1 ◇ X0)) ◇ X0 = X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef123 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef11 ef23 | exact superpose ef23 ef11
  have ef124 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X0 ◇ (X2 ◇ X0)) ◇ X0 := by
    first | exact superpose ef11 ef18 | exact superpose ef18 ef11
  have ef298 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1) := by
    first | exact superpose ef31 ef5 | exact superpose ef5 ef31
  have ef305 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X2 ◇ (X3 ◇ X0)) ◇ X0 := by
    first | exact superpose ef31 ef18 | exact superpose ef18 ef31
  have ef400 (X0 X1 X2 X3 : G) : X0 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef23 | exact superpose ef23 ef124
  have ef496 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X2 ◇ X3) ◇ X0) = (X3 ◇ (X4 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef20 | exact superpose ef20 ef124
  have ef548 (X0 X2 X3 X4 : G) : X0 ◇ ((X4 ◇ X3) ◇ X0) = X0 ◇ ((X2 ◇ X3) ◇ X0) := by
    first | exact superpose ef400 ef496 | exact superpose ef496 ef400
  have ef601 (X0 X1 X2 X3 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇
      (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef18 ef305 | exact superpose ef305 ef18
  have ef700 (X0 X1 X3 : G) : (X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef601 | exact superpose ef601 ef298
  have ef764 (X0 X1 X2 : G) :
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef25 ef23 | exact superpose ef23 ef25
  have ef788 (X0 X1 X2 : G) :
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef700 ef764 | exact superpose ef764 ef700
  have ef808 (X0 X1 X2 : G) :
      X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef400 ef788 | exact superpose ef788 ef400
  have ef824 (X0 X1 X2 : G) : X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇ (X1 ◇ X0) := by
    first | exact superpose ef7 ef808 | exact superpose ef808 ef7
  have ef1405 (X0 X1 X2 X3 : G) :
      (X1 ◇ X2) ◇ X0 = (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    first | exact superpose ef548 ef7 | exact superpose ef7 ef548
  have ef3392 (X0 X1 X2 X3 : G) :
      (X3 ◇ X2) ◇ X0 = (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    first | exact superpose ef5 ef824 | exact superpose ef824 ef5
  have ef3718 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ X0 = (X3 ◇ X2) ◇ X0 := by
    first | exact superpose ef1405 ef3392 | exact superpose ef3392 ef1405
  have ef4672 (X0 : G) : x ≠ (x ◇ x) ◇ ((((y ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)) ◇ ((X0 ◇ x) ◇ x)) := by
    first | exact superpose ef3718 ef6 | exact superpose ef6 ef3718
  have ef4716 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) = (X4 ◇ (X3 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef3718 ef824 | exact superpose ef824 ef3718
  have ef4789 (X0 : G) : x ≠ (x ◇ x) ◇ (x ◇ ((x ◇ ((X0 ◇ x) ◇ x)) ◇ x)) := by
    first | exact superpose ef4716 ef4672 | exact superpose ef4672 ef4716
  subsumption ef4789 ef123

theorem Equation832_termStructuralFrom_Equation690 :
    Law832.TermStructuralFrom Law690 := by
  intro G M hGL
  have h : Equation690 G := Law690.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law832.models_iff]
    exact fun x y ↦ @aux690_832 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv690_b17ab2c2 G M h (z 0) (z 1)).symm⟩

/-- Equation 845 `x = x ◇ ((y ◇ y) ◇ (y ◇ x))` holds of the term `x □ y := (x ◇ x) ◇ y` over any
magma satisfying equation 690 `x = y ◇ (x ◇ ((z ◇ y) ◇ x))`. -/
private theorem aux690_845 [Magma G] (h : Equation690 G) (x y : G) :
    x = (x ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ y) ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 : x ≠ (x ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((y ◇ y) ◇ x)) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0) = X1 ◇ ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X0) := superpose ef5 ef5
  have ef11 (X0 X1 X4 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) = X4 := superpose ef7 ef7
  have ef18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)) = X2 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef20 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X1) = (X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef25 (X0 X1 : G) :
      (X0 ◇ (X1 ◇ X0)) ◇ X0 = X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef123 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef11 ef23 | exact superpose ef23 ef11
  have ef124 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X0 ◇ (X2 ◇ X0)) ◇ X0 := by
    first | exact superpose ef11 ef18 | exact superpose ef18 ef11
  have ef298 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1) := by
    first | exact superpose ef31 ef5 | exact superpose ef5 ef31
  have ef305 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X2 ◇ (X3 ◇ X0)) ◇ X0 := by
    first | exact superpose ef31 ef18 | exact superpose ef18 ef31
  have ef400 (X0 X1 X2 X3 : G) : X0 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef23 | exact superpose ef23 ef124
  have ef496 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X2 ◇ X3) ◇ X0) = (X3 ◇ (X4 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef20 | exact superpose ef20 ef124
  have ef548 (X0 X2 X3 X4 : G) : X0 ◇ ((X4 ◇ X3) ◇ X0) = X0 ◇ ((X2 ◇ X3) ◇ X0) := by
    first | exact superpose ef400 ef496 | exact superpose ef496 ef400
  have ef601 (X0 X1 X2 X3 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇
      (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef18 ef305 | exact superpose ef305 ef18
  have ef700 (X0 X1 X3 : G) : (X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef601 | exact superpose ef601 ef298
  have ef764 (X0 X1 X2 : G) :
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef25 ef23 | exact superpose ef23 ef25
  have ef788 (X0 X1 X2 : G) :
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef700 ef764 | exact superpose ef764 ef700
  have ef808 (X0 X1 X2 : G) :
      X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef400 ef788 | exact superpose ef788 ef400
  have ef824 (X0 X1 X2 : G) : X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇ (X1 ◇ X0) := by
    first | exact superpose ef7 ef808 | exact superpose ef808 ef7
  have ef1411 (X0 X1 X2 : G) : X1 ◇ X0 = (X0 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef548 ef18 | exact superpose ef18 ef548
  have ef3392 (X0 X1 X2 X3 : G) :
      (X3 ◇ X2) ◇ X0 = (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    first | exact superpose ef5 ef824 | exact superpose ef824 ef5
  have ef3718 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ X0 = (X3 ◇ X2) ◇ X0 := by
    first | exact superpose ef1411 ef3392 | exact superpose ef3392 ef1411
  have ef4672 (X0 : G) : x ≠ (x ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ ((X0 ◇ y) ◇ x)) := by
    first | exact superpose ef3718 ef6 | exact superpose ef6 ef3718
  have ef4716 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) = (X4 ◇ (X3 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef3718 ef824 | exact superpose ef824 ef3718
  have ef4789 (X0 : G) : x ≠ (x ◇ x) ◇ (x ◇ ((x ◇ ((X0 ◇ y) ◇ x)) ◇ x)) := by
    first | exact superpose ef4716 ef4672 | exact superpose ef4672 ef4716
  subsumption ef4789 ef123

theorem Equation845_termStructuralFrom_Equation690 :
    Law845.TermStructuralFrom Law690 := by
  intro G M hGL
  have h : Equation690 G := Law690.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law845.models_iff]
    exact fun x y ↦ @aux690_845 G M h x y
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv690_b17ab2c2 G M h (z 0) (z 1)).symm⟩

/-- Equation 860 `x = x ◇ ((y ◇ z) ◇ (z ◇ x))` holds of the term `x □ y := (x ◇ x) ◇ y` over any
magma satisfying equation 690 `x = y ◇ (x ◇ ((z ◇ y) ◇ x))`. -/
private theorem aux690_860 [Magma G] (h : Equation690 G) (x y z : G) :
    x = (x ◇ x) ◇ ((((y ◇ y) ◇ z) ◇ ((y ◇ y) ◇ z)) ◇ ((z ◇ z) ◇ x)) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 : x ≠ (x ◇ x) ◇ ((((y ◇ y) ◇ z) ◇ ((y ◇ y) ◇ z)) ◇ ((z ◇ z) ◇ x)) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0) = X1 ◇ ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X0) := superpose ef5 ef5
  have ef11 (X0 X1 X4 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) = X4 := superpose ef7 ef7
  have ef18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)) = X2 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef20 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X1) = (X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef25 (X0 X1 : G) :
      (X0 ◇ (X1 ◇ X0)) ◇ X0 = X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef123 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef11 ef23 | exact superpose ef23 ef11
  have ef124 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X0 ◇ (X2 ◇ X0)) ◇ X0 := by
    first | exact superpose ef11 ef18 | exact superpose ef18 ef11
  have ef298 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1) := by
    first | exact superpose ef31 ef5 | exact superpose ef5 ef31
  have ef305 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X2 ◇ (X3 ◇ X0)) ◇ X0 := by
    first | exact superpose ef31 ef18 | exact superpose ef18 ef31
  have ef400 (X0 X1 X2 X3 : G) : X0 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef23 | exact superpose ef23 ef124
  have ef496 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X2 ◇ X3) ◇ X0) = (X3 ◇ (X4 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef20 | exact superpose ef20 ef124
  have ef548 (X0 X2 X3 X4 : G) : X0 ◇ ((X4 ◇ X3) ◇ X0) = X0 ◇ ((X2 ◇ X3) ◇ X0) := by
    first | exact superpose ef400 ef496 | exact superpose ef496 ef400
  have ef601 (X0 X1 X2 X3 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇
      (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef18 ef305 | exact superpose ef305 ef18
  have ef700 (X0 X1 X3 : G) : (X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef601 | exact superpose ef601 ef298
  have ef764 (X0 X1 X2 : G) :
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef25 ef23 | exact superpose ef23 ef25
  have ef788 (X0 X1 X2 : G) :
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef700 ef764 | exact superpose ef764 ef700
  have ef808 (X0 X1 X2 : G) :
      X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef400 ef788 | exact superpose ef788 ef400
  have ef824 (X0 X1 X2 : G) : X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇ (X1 ◇ X0) := by
    first | exact superpose ef7 ef808 | exact superpose ef808 ef7
  have ef1405 (X0 X1 X2 X3 : G) :
      (X1 ◇ X2) ◇ X0 = (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    first | exact superpose ef548 ef7 | exact superpose ef7 ef548
  have ef3392 (X0 X1 X2 X3 : G) :
      (X3 ◇ X2) ◇ X0 = (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    first | exact superpose ef5 ef824 | exact superpose ef824 ef5
  have ef3718 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ X0 = (X3 ◇ X2) ◇ X0 := by
    first | exact superpose ef1405 ef3392 | exact superpose ef3392 ef1405
  have ef4672 (X0 : G) : x ≠ (x ◇ x) ◇ ((((X0 ◇ y) ◇ z) ◇ ((X0 ◇ y) ◇ z)) ◇ ((z ◇ z) ◇ x)) := by
    first | exact superpose ef3718 ef6 | exact superpose ef6 ef3718
  have ef4716 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) = (X4 ◇ (X3 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2) := by
    first | exact superpose ef3718 ef824 | exact superpose ef824 ef3718
  have ef4789 : x ≠ (x ◇ x) ◇ (x ◇ ((x ◇ ((z ◇ z) ◇ x)) ◇ x)) := by
    first | exact superpose ef4716 ef4672 | exact superpose ef4672 ef4716
  subsumption ef4789 ef123

theorem Equation860_termStructuralFrom_Equation690 :
    Law860.TermStructuralFrom Law690 := by
  intro G M hGL
  have h : Equation690 G := Law690.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op x x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law860.models_iff]
    exact fun x y z ↦ @aux690_860 G M h x y z
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv690_b17ab2c2 G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := (((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)`
of equation 690 `x = y ◇ (x ◇ ((z ◇ y) ◇ x))` can be undone: the operation is recovered as
`x ◇ y = x ◇ (y ◇ y)` read in `□`. -/
private theorem inv690_c343535e [Magma G] (h : Equation690 G) (x y : G) :
    (((x ◇ x) ◇ (x ◇ x)) ◇ (((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇ x))) ◇ (((x ◇ x) ◇
      (x ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y))) = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 :
      (((x ◇ x) ◇ (x ◇ x)) ◇ (((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇ x))) ◇ (((x ◇ x) ◇
      (x ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y))) ≠ x ◇ y := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0) = X1 ◇ ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X0) := superpose ef5 ef5
  have ef11 (X0 X1 X4 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) = X4 := superpose ef7 ef7
  have ef16 (X0 X1 X2 X3 X4 : G) :
      X2 ◇ ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ ((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2))) ◇
      ((X0 ◇ X1) ◇ X2) := superpose ef7 ef7
  have ef18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)) = X2 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef20 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X1) = (X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef123 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef11 ef23 | exact superpose ef23 ef11
  have ef124 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X0 ◇ (X2 ◇ X0)) ◇ X0 := by
    first | exact superpose ef11 ef18 | exact superpose ef18 ef11
  have ef220 (X0 X1 X2 X3 : G) : (X3 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef123 | exact superpose ef123 ef8
  have ef305 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X2 ◇ (X3 ◇ X0)) ◇ X0 := by
    first | exact superpose ef31 ef18 | exact superpose ef18 ef31
  have ef400 (X0 X1 X2 X3 : G) : X0 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef23 | exact superpose ef23 ef124
  have ef496 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X2 ◇ X3) ◇ X0) = (X3 ◇ (X4 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef20 | exact superpose ef20 ef124
  have ef548 (X0 X2 X3 X4 : G) : X0 ◇ ((X4 ◇ X3) ◇ X0) = X0 ◇ ((X2 ◇ X3) ◇ X0) := by
    first | exact superpose ef400 ef496 | exact superpose ef496 ef400
  have ef588 (X0 X1 X2 X4 X5 : G) :
      (X0 ◇ (X1 ◇ X2)) ◇ X2 = (X4 ◇ (X5 ◇ X2)) ◇ X2 := superpose ef305 ef305
  have ef627 (X0 X1 X2 X3 X4 : G) : X2 ◇ (X3 ◇ X2) = (X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2) := by
    first | exact superpose ef305 ef23 | exact superpose ef23 ef305
  have ef1315 (X0 X1 X2 X3 X4 X5 : G) :
      X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)) = ((X1 ◇ X2) ◇ X0) ◇ ((X3 ◇ (X4 ◇ X5)) ◇ ((X1 ◇ X2) ◇ X0)) := by
    first | exact superpose ef16 ef8 | exact superpose ef8 ef16
  have ef1932 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X1) := by
    first | exact superpose ef18 ef548 | exact superpose ef548 ef18
  have ef2757 (X0 X1 : G) :
      x ◇ y ≠ (((x ◇ x) ◇ (x ◇ x)) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ ((X0 ◇ (X1 ◇ y)) ◇ y)) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ ((X0 ◇ (X1 ◇ y)) ◇ y)) ◇ x))) ◇ (((x ◇ x) ◇
      (x ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ ((X0 ◇ (X1 ◇ y)) ◇ y)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ ((X0 ◇ (X1 ◇ y)) ◇ y))) := by
    first | exact superpose ef588 ef6 | exact superpose ef6 ef588
  have ef2807 (X0 X1 : G) :
      x ◇ y ≠ ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ ((X0 ◇ (X1 ◇ y)) ◇ y)) ◇
      ((((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ ((X0 ◇ (X1 ◇ y)) ◇ y)) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ ((X0 ◇ (X1 ◇ y)) ◇ y)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ ((X0 ◇ (X1 ◇ y)) ◇ y))) := by
    first | exact superpose ef627 ef2757 | exact superpose ef2757 ef627
  have ef2868 (X0 X1 : G) :
      x ◇ y ≠ x ◇ (((X0 ◇ (X1 ◇ y)) ◇ y) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ ((X0 ◇ (X1 ◇ y)) ◇ y))) := by
    first | exact superpose ef1315 ef2807 | exact superpose ef2807 ef1315
  have ef2875 (X0 X1 : G) : x ◇ y ≠ x ◇ (((X0 ◇ (X1 ◇ y)) ◇ y) ◇ (y ◇ ((X0 ◇ (X1 ◇ y)) ◇ y))) := by
    first | exact superpose ef1932 ef2868 | exact superpose ef2868 ef1932
  have ef2881 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef220 ef2875 | exact superpose ef2875 ef220
  exact absurd rfl ef2881

set_option maxHeartbeats 600000 in
/-- Equation 1426 `x = (x ◇ x) ◇ (x ◇ (x ◇ x))` holds of the term
`x □ y := (((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)` over any magma
satisfying equation 690 `x = y ◇ (x ◇ ((z ◇ y) ◇ x))`. -/
private theorem aux690_1426 [Magma G] (h : Equation690 G) (x : G) :
    x = (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇
      (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))))) ◇ ((((x ◇ x) ◇ (x ◇
      x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇
      (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))))) ◇ ((((x ◇ x) ◇ (x ◇
      x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0) = X1 ◇ ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X0) := superpose ef5 ef5
  have ef11 (X0 X1 X4 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) = X4 := superpose ef7 ef7
  have ef14 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X4 ◇ X1) ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ ((X0 ◇ ((X4 ◇ X1) ◇ X0)) ◇ X0) := by
    first | exact superpose ef5 ef7 | exact superpose ef7 ef5
  have ef17 (X0 X1 X2 X3 : G) : X0 ◇ (X3 ◇ X0) = ((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X0) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)) = X2 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef20 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X1) = (X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef21 (X0 X1 X2 X3 X4 X5 : G) :
      X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ X4) = ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇
      ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ X4)) ◇ X4) := superpose ef8 ef8
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef25 (X0 X1 : G) :
      (X0 ◇ (X1 ◇ X0)) ◇ X0 = X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef33 (X0 X1 X2 X3 X4 X5 : G) :
      (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0 = (X3 ◇ ((X4 ◇ X5) ◇ X3)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef37 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0 = X4 ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef123 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef11 ef23 | exact superpose ef23 ef11
  have ef124 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X0 ◇ (X2 ◇ X0)) ◇ X0 := by
    first | exact superpose ef11 ef18 | exact superpose ef18 ef11
  have ef298 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1) := by
    first | exact superpose ef31 ef5 | exact superpose ef5 ef31
  have ef305 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X2 ◇ (X3 ◇ X0)) ◇ X0 := by
    first | exact superpose ef31 ef18 | exact superpose ef18 ef31
  have ef400 (X0 X1 X2 X3 : G) : X0 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef23 | exact superpose ef23 ef124
  have ef444 (X0 X1 X2 X3 : G) :
      X2 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇
      ((X2 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X2)) ◇ X2) := by
    first | exact superpose ef17 ef20 | exact superpose ef20 ef17
  have ef556 (X0 X1 X2 X3 : G) :
      X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2) = X2 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X2) := by
    first | exact superpose ef400 ef444 | exact superpose ef444 ef400
  have ef601 (X0 X1 X2 X3 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇
      (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef18 ef305 | exact superpose ef305 ef18
  have ef627 (X0 X1 X2 X3 X4 : G) : X2 ◇ (X3 ◇ X2) = (X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2) := by
    first | exact superpose ef305 ef23 | exact superpose ef23 ef305
  have ef675 (X0 : G) :
      x ≠ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇
      (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))))) ◇ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      ((x ◇ (X0 ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))))) := by
    first | exact superpose ef305 ef6 | exact superpose ef6 ef305
  have ef698 (X0 : G) :
      x ≠ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇
      (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))))) ◇ ((((x ◇ x) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))))) := by
    first | exact superpose ef298 ef675 | exact superpose ef675 ef298
  have ef706 (X0 X1 X3 : G) : (X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef601 | exact superpose ef601 ef298
  have ef726 (X0 : G) :
      x ≠ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))))) ◇ ((((x ◇ x) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇
      (X0 ◇ x)) ◇ x)) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))))) := by
    first | exact superpose ef627 ef698 | exact superpose ef698 ef627
  have ef729 :
      x ≠ ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) ◇ ((((x ◇ x) ◇ (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇
      ((x ◇ (x ◇ x)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef400 ef726 | exact superpose ef726 ef400
  have ef732 :
      x ≠ ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) ◇ ((((x ◇ x) ◇ (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇
      ((x ◇ (x ◇ x)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef556 ef729 | exact superpose ef729 ef556
  have ef735 :
      x ≠ ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef706 ef732 | exact superpose ef732 ef706
  have ef738 :
      x ≠ ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef556 ef735 | exact superpose ef735 ef556
  have ef741 :
      x ≠ ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef400 ef738 | exact superpose ef738 ef400
  have ef788 (X0 X1 X2 : G) :
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef25 ef23 | exact superpose ef23 ef25
  have ef796 (X0 X1 X2 X3 : G) :
      (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) =
      (X2 ◇ (X3 ◇ X2)) ◇ (((((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    first | exact superpose ef25 ef20 | exact superpose ef20 ef25
  have ef801 (X0 X1 X2 X3 : G) :
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ ((X0 ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = X3 ◇
      (((((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef25 ef8 | exact superpose ef8 ef25
  have ef802 (X0 X1 X2 X3 : G) :
      (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇
      X0) = X3 ◇ (((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef706 ef801 | exact superpose ef801 ef706
  have ef804 (X0 X1 X2 X3 : G) :
      (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) = (X2 ◇
      (X3 ◇ X2)) ◇
      (((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0)) ◇
      (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    first | exact superpose ef706 ef796 | exact superpose ef796 ef706
  have ef812 (X0 X1 X2 : G) :
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef706 ef788 | exact superpose ef788 ef706
  have ef826 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = X3 ◇
      ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0)) ◇
      (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef400 ef802 | exact superpose ef802 ef400
  have ef827 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) = (X2 ◇ (X3 ◇ X2)) ◇
      ((X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    first | exact superpose ef400 ef804 | exact superpose ef804 ef400
  have ef832 (X0 X1 X2 : G) :
      X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef400 ef812 | exact superpose ef812 ef400
  have ef842 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = X3 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0) := by
    first | exact superpose ef7 ef826 | exact superpose ef826 ef7
  have ef843 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) = (X2 ◇ (X3 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X0) := by
    first | exact superpose ef7 ef827 | exact superpose ef827 ef7
  have ef848 (X0 X1 X2 : G) : X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇ (X1 ◇ X0) := by
    first | exact superpose ef7 ef832 | exact superpose ef832 ef7
  have ef2179 (X0 X1 X2 X3 X4 X5 X6 : G) :
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ ((X0 ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇
      (((((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef33 ef23 | exact superpose ef23 ef33
  have ef2199 (X0 X1 X2 X3 X4 X5 X6 : G) :
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ ((X0 ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇
      X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) ◇ (X0 ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef848 ef2179 | exact superpose ef2179 ef848
  have ef2295 (X0 X1 X2 X3 X4 X5 X6 : G) :
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef14 ef2199 | exact superpose ef2199 ef14
  have ef2354 (X0 X1 X2 X3 X4 X5 X6 : G) :
      (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇
      X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇
      (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef706 ef2295 | exact superpose ef2295 ef706
  have ef2379 (X0 X1 X2 X3 X4 X5 X6 : G) :
      (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0) := by
    first | exact superpose ef7 ef2354 | exact superpose ef2354 ef7
  have ef2396 (X0 X1 X2 X3 X4 X5 X6 : G) :
      X0 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0)) ◇ X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0) := by
    first | exact superpose ef843 ef2379 | exact superpose ef2379 ef843
  have ef2411 (X0 X1 X2 X3 X4 X5 X6 : G) :
      X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0) := by
    first | exact superpose ef8 ef2396 | exact superpose ef2396 ef8
  have ef2575 (X0 X1 X2 X3 X4 : G) :
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) = X4 ◇
      ((((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)))) ◇
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0))) := by
    first | exact superpose ef37 ef25 | exact superpose ef25 ef37
  have ef2623 (X0 X1 X2 X3 X4 : G) :
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) = X4 ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0) ◇ ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0))) := by
    first | exact superpose ef848 ef2575 | exact superpose ef2575 ef848
  have ef2677 (X0 X1 X2 X3 X4 : G) :
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) = X4 ◇ (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) ◇
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0))) := by
    first | exact superpose ef842 ef2623 | exact superpose ef2623 ef842
  have ef2716 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) = X4 ◇
      (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) ◇
      (X0 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ X0))) := by
    first | exact superpose ef2411 ef2677 | exact superpose ef2677 ef2411
  have ef2737 (X0 X1 X2 X3 X4 : G) :
      X4 ◇ X0 = (X0 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) := by
    first | exact superpose ef123 ef2716 | exact superpose ef2716 ef123
  have ef2754 (X0 X1 X2 X3 X4 : G) :
      X4 ◇ X0 = (X0 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ X0)) ◇
      (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) := by
    first | exact superpose ef706 ef2737 | exact superpose ef2737 ef706
  have ef2771 (X0 X1 X2 X3 X4 : G) : X4 ◇ X0 = (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 := by
    first | exact superpose ef7 ef2754 | exact superpose ef2754 ef7
  have ef2960 (X0 X1 X2 X3 X4 X5 X6 : G) :
      ((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0) ◇ (X0 ◇
      ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) = (X2 ◇ (X6 ◇ X2)) ◇
      ((((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0)) := by
    first | exact superpose ef21 ef20 | exact superpose ef20 ef21
  have ef3075 (X0 X1 X2 X3 X4 X5 X6 : G) :
      ((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) = (X2 ◇ (X6 ◇ X2)) ◇
      (X0 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0)) ◇ X0)) := by
    first | exact superpose ef2411 ef2960 | exact superpose ef2960 ef2411
  have ef3144 (X0 X1 X2 X3 X4 X5 X6 : G) :
      ((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) = (X2 ◇ (X6 ◇ X2)) ◇
      (X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0)) := by
    first | exact superpose ef8 ef3075 | exact superpose ef3075 ef8
  have ef3175 (X0 X2 X6 : G) :
      ((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X6 ◇ X2)) ◇
      (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := by
    first | exact superpose ef2771 ef3144 | exact superpose ef3144 ef2771
  have ef3197 (X0 X2 X6 : G) :
      (X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X6 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := by
    first | exact superpose ef706 ef3175 | exact superpose ef3175 ef706
  have ef3264 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X2 = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X2 := by
    first | exact superpose ef25 ef2771 | exact superpose ef2771 ef25
  have ef3373 :
      x ≠ ((((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) ◇ (x ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2771 ef741 | exact superpose ef741 ef2771
  have ef3542 :
      x ≠ (x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2771 ef3373 | exact superpose ef3373 ef2771
  have ef3607 :
      x ≠ (x ◇ (x ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef3264 ef3542 | exact superpose ef3542 ef3264
  have ef3627 :
      x ≠ (x ◇ (x ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef3264 ef3607 | exact superpose ef3607 ef3264
  have ef3643 : x ≠ (x ◇ (x ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef3197 ef3627 | exact superpose ef3627 ef3197
  have ef3658 : x ≠ (x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef5 ef3643 | exact superpose ef3643 ef5
  subsumption ef3658 ef18

theorem Equation1426_termStructuralFrom_Equation690 :
    Law1426.TermStructuralFrom Law690 := by
  intro G M hGL
  have h : Equation690 G := Law690.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op y (M.op y x))) (M.op (M.op (M.op x x) (M.op x y)) y))⟩, ?_, ?_, ?_⟩
  · rw [@Law1426.models_iff]
    exact fun x ↦ @aux690_1426 G M h x
  · exact ⟨(tm (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))) (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 1) (Term.var 1))), funext fun z ↦ (@inv690_c343535e G M h (z 0) (z 1)).symm⟩

/-- Equation 1451 `x = (x ◇ y) ◇ (y ◇ (x ◇ x))` holds of the term
`x □ y := (((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)` over any magma
satisfying equation 690 `x = y ◇ (x ◇ ((z ◇ y) ◇ x))`. -/
private theorem aux690_1451 [Magma G] (h : Equation690 G) (x y : G) :
    x = (((((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)))) ◇ (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ (((y ◇ y) ◇
      (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      (((y ◇ y) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y))))) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      (((y ◇ y) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))))) ◇ ((((y ◇ y) ◇ (y ◇
      y)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ (((y ◇ y) ◇ (y ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)))) ◇ (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ (((y ◇ y) ◇
      (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      (((y ◇ y) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y))))) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      (((y ◇ y) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))))) ◇ ((((y ◇ y) ◇ (y ◇
      y)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ (((y ◇ y) ◇ (y ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0) = X1 ◇ ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X0) := superpose ef5 ef5
  have ef11 (X0 X1 X4 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) = X4 := superpose ef7 ef7
  have ef18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)) = X2 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef20 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X1) = (X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef25 (X0 X1 : G) :
      (X0 ◇ (X1 ◇ X0)) ◇ X0 = X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef123 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef11 ef23 | exact superpose ef23 ef11
  have ef124 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X0 ◇ (X2 ◇ X0)) ◇ X0 := by
    first | exact superpose ef11 ef18 | exact superpose ef18 ef11
  have ef220 (X0 X1 X2 X3 : G) : (X3 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef123 | exact superpose ef123 ef8
  have ef298 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1) := by
    first | exact superpose ef31 ef5 | exact superpose ef5 ef31
  have ef305 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X2 ◇ (X3 ◇ X0)) ◇ X0 := by
    first | exact superpose ef31 ef18 | exact superpose ef18 ef31
  have ef400 (X0 X1 X2 X3 : G) : X0 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef23 | exact superpose ef23 ef124
  have ef496 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X2 ◇ X3) ◇ X0) = (X3 ◇ (X4 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef20 | exact superpose ef20 ef124
  have ef548 (X0 X2 X3 X4 : G) : X0 ◇ ((X4 ◇ X3) ◇ X0) = X0 ◇ ((X2 ◇ X3) ◇ X0) := by
    first | exact superpose ef400 ef496 | exact superpose ef496 ef400
  have ef601 (X0 X1 X2 X3 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇
      (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef18 ef305 | exact superpose ef305 ef18
  have ef627 (X0 X1 X2 X3 X4 : G) : X2 ◇ (X3 ◇ X2) = (X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2) := by
    first | exact superpose ef305 ef23 | exact superpose ef23 ef305
  have ef704 (X0 X1 X3 : G) : (X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef601 | exact superpose ef601 ef298
  have ef778 (X0 X1 X2 : G) :
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef25 ef23 | exact superpose ef23 ef25
  have ef802 (X0 X1 X2 : G) :
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef704 ef778 | exact superpose ef778 ef704
  have ef822 (X0 X1 X2 : G) :
      X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef400 ef802 | exact superpose ef802 ef400
  have ef838 (X0 X1 X2 : G) : X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇ (X1 ◇ X0) := by
    first | exact superpose ef7 ef822 | exact superpose ef822 ef7
  have ef1251 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X1) := by
    first | exact superpose ef18 ef548 | exact superpose ef548 ef18
  have ef2987 :
      x ≠ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)))) ◇ (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇ (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y))))) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))))) ◇ ((((y ◇ y) ◇ (y ◇
      y)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ ((((x ◇ x) ◇
      (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef298 ef6 | exact superpose ef6 ef298
  have ef2989 (X0 X1 X2 X3 X4 : G) :
      X4 ◇ (X0 ◇ (X1 ◇ X0)) = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef8 | exact superpose ef8 ef298
  have ef2996 (X0 X1 X2 X3 : G) : (X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)) = (X3 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef23 | exact superpose ef23 ef298
  have ef3073 :
      x ≠ ((((y ◇ y) ◇ (y ◇ y)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ ((((x ◇
      x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇ (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)))) ◇ ((((y ◇ y) ◇ (y ◇
      y)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ ((((x ◇ x) ◇
      (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef627 ef2987 | exact superpose ef2987 ef627
  have ef3086 :
      x ≠ ((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇ (((((x ◇ x) ◇
      (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2989 ef3073 | exact superpose ef3073 ef2989
  have ef3089 :
      x ≠ ((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2989 ef3086 | exact superpose ef3086 ef2989
  have ef3091 :
      x ≠ ((((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2996 ef3089 | exact superpose ef3089 ef2996
  have ef3093 :
      x ≠ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ y)) ◇ y) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2996 ef3091 | exact superpose ef3091 ef2996
  have ef3095 :
      x ≠ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ y)) ◇ y) ◇
      (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef1251 ef3093 | exact superpose ef3093 ef1251
  have ef3097 : x ≠ (y ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ y)) ◇ y) ◇ (y ◇ x)) := by
    first | exact superpose ef220 ef3095 | exact superpose ef3095 ef220
  have ef3099 : x ≠ (y ◇ x) ◇ (x ◇ ((x ◇ (y ◇ x)) ◇ x)) := by
    first | exact superpose ef838 ef3097 | exact superpose ef3097 ef838
  subsumption ef3099 ef5

theorem Equation1451_termStructuralFrom_Equation690 :
    Law1451.TermStructuralFrom Law690 := by
  intro G M hGL
  have h : Equation690 G := Law690.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op y (M.op y x))) (M.op (M.op (M.op x x) (M.op x y)) y))⟩, ?_, ?_, ?_⟩
  · rw [@Law1451.models_iff]
    exact fun x y ↦ @aux690_1451 G M h x y
  · exact ⟨(tm (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))) (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 1) (Term.var 1))), funext fun z ↦ (@inv690_c343535e G M h (z 0) (z 1)).symm⟩

set_option maxHeartbeats 600000 in
/-- Equation 1478 `x = (y ◇ x) ◇ (x ◇ (x ◇ x))` holds of the term
`x □ y := (((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)` over any magma
satisfying equation 690 `x = y ◇ (x ◇ ((z ◇ y) ◇ x))`. -/
private theorem aux690_1478 [Magma G] (h : Equation690 G) (x y : G) :
    x = (((((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇
      (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))))) ◇
      (((((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))))) ◇ ((((x ◇ x) ◇ (x ◇
      x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇
      (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))))) ◇
      (((((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))))) ◇ ((((x ◇ x) ◇ (x ◇
      x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0) = X1 ◇ ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X0) := superpose ef5 ef5
  have ef11 (X0 X1 X4 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) = X4 := superpose ef7 ef7
  have ef14 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X4 ◇ X1) ◇ X0) = (X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ ((X0 ◇ ((X4 ◇ X1) ◇ X0)) ◇ X0) := by
    first | exact superpose ef5 ef7 | exact superpose ef7 ef5
  have ef17 (X0 X1 X2 X3 : G) : X0 ◇ (X3 ◇ X0) = ((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X0) := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)) = X2 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef20 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X1) = (X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef21 (X0 X1 X2 X3 X4 X5 : G) :
      X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ X4) = ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇
      ((X4 ◇ ((X5 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ X4)) ◇ X4) := superpose ef8 ef8
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef25 (X0 X1 : G) :
      (X0 ◇ (X1 ◇ X0)) ◇ X0 = X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef33 (X0 X1 X2 X3 X4 X5 : G) :
      (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0 = (X3 ◇ ((X4 ◇ X5) ◇ X3)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef37 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0 = X4 ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef123 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef11 ef23 | exact superpose ef23 ef11
  have ef124 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X0 ◇ (X2 ◇ X0)) ◇ X0 := by
    first | exact superpose ef11 ef18 | exact superpose ef18 ef11
  have ef298 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1) := by
    first | exact superpose ef31 ef5 | exact superpose ef5 ef31
  have ef305 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X2 ◇ (X3 ◇ X0)) ◇ X0 := by
    first | exact superpose ef31 ef18 | exact superpose ef18 ef31
  have ef400 (X0 X1 X2 X3 : G) : X0 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef23 | exact superpose ef23 ef124
  have ef444 (X0 X1 X2 X3 : G) :
      X2 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇
      ((X2 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X2)) ◇ X2) := by
    first | exact superpose ef17 ef20 | exact superpose ef20 ef17
  have ef556 (X0 X1 X2 X3 : G) :
      X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2) = X2 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X2) := by
    first | exact superpose ef400 ef444 | exact superpose ef444 ef400
  have ef601 (X0 X1 X2 X3 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇
      (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef18 ef305 | exact superpose ef305 ef18
  have ef627 (X0 X1 X2 X3 X4 : G) : X2 ◇ (X3 ◇ X2) = (X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2) := by
    first | exact superpose ef305 ef23 | exact superpose ef23 ef305
  have ef675 (X0 : G) :
      x ≠ (((((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇
      (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))))) ◇ (((((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇
      (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇
      x))) ◇ (((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))))) := by
    first | exact superpose ef305 ef6 | exact superpose ef6 ef305
  have ef698 (X0 : G) :
      x ≠ (((((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇
      (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))))) ◇ ((((x ◇ x) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))))) := by
    first | exact superpose ef298 ef675 | exact superpose ef675 ef298
  have ef706 (X0 X1 X3 : G) : (X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef601 | exact superpose ef601 ef298
  have ef726 (X0 : G) :
      x ≠ (((((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)))) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      ((x ◇ (X0 ◇ x)) ◇ x)) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))))) ◇ ((((x ◇ x) ◇ (x ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇
      (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇
      (X0 ◇ x)) ◇ x)) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ ((x ◇ (X0 ◇ x)) ◇ x))))) := by
    first | exact superpose ef627 ef698 | exact superpose ef698 ef627
  have ef729 :
      x ≠ (((((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)))) ◇ (((x ◇
      ((x ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))))) ◇ ((((x ◇ x) ◇ (x ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x)) ◇ (x ◇
      ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef400 ef726 | exact superpose ef726 ef400
  have ef732 :
      x ≠ (((((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))))) ◇ ((((x ◇ x) ◇
      (x ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef556 ef729 | exact superpose ef729 ef556
  have ef735 :
      x ≠ (((((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))))) ◇ (((x ◇
      ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef706 ef732 | exact superpose ef732 ef706
  have ef738 :
      x ≠ (((((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x)))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ (x ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ x)) ◇ x))))) ◇ (((x ◇
      ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef556 ef735 | exact superpose ef735 ef556
  have ef741 :
      x ≠ ((((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ y)) ◇ x)))) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ y)) ◇ x))))) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef627 ef738 | exact superpose ef738 ef627
  have ef744 :
      x ≠ ((((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ y)) ◇ x)))) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ (x ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ y)) ◇ x))))) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef556 ef741 | exact superpose ef741 ef556
  have ef790 (X0 X1 X2 : G) :
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef25 ef23 | exact superpose ef23 ef25
  have ef798 (X0 X1 X2 X3 : G) :
      (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) =
      (X2 ◇ (X3 ◇ X2)) ◇ (((((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    first | exact superpose ef25 ef20 | exact superpose ef20 ef25
  have ef803 (X0 X1 X2 X3 : G) :
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ ((X0 ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = X3 ◇
      (((((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef25 ef8 | exact superpose ef8 ef25
  have ef804 (X0 X1 X2 X3 : G) :
      (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇
      X0) = X3 ◇ (((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef706 ef803 | exact superpose ef803 ef706
  have ef806 (X0 X1 X2 X3 : G) :
      (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) = (X2 ◇
      (X3 ◇ X2)) ◇
      (((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0)) ◇
      (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    first | exact superpose ef706 ef798 | exact superpose ef798 ef706
  have ef814 (X0 X1 X2 : G) :
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef706 ef790 | exact superpose ef790 ef706
  have ef828 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = X3 ◇
      ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0)) ◇
      (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef400 ef804 | exact superpose ef804 ef400
  have ef829 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) = (X2 ◇ (X3 ◇ X2)) ◇
      ((X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    first | exact superpose ef400 ef806 | exact superpose ef806 ef400
  have ef834 (X0 X1 X2 : G) :
      X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef400 ef814 | exact superpose ef814 ef400
  have ef844 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = X3 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0) := by
    first | exact superpose ef7 ef828 | exact superpose ef828 ef7
  have ef845 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) = (X2 ◇ (X3 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X0) := by
    first | exact superpose ef7 ef829 | exact superpose ef829 ef7
  have ef850 (X0 X1 X2 : G) : X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇ (X1 ◇ X0) := by
    first | exact superpose ef7 ef834 | exact superpose ef834 ef7
  have ef2181 (X0 X1 X2 X3 X4 X5 X6 : G) :
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ ((X0 ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇
      (((((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef33 ef23 | exact superpose ef23 ef33
  have ef2201 (X0 X1 X2 X3 X4 X5 X6 : G) :
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ ((X0 ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇
      X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) ◇ (X0 ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef850 ef2181 | exact superpose ef2181 ef850
  have ef2297 (X0 X1 X2 X3 X4 X5 X6 : G) :
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef14 ef2201 | exact superpose ef2201 ef14
  have ef2356 (X0 X1 X2 X3 X4 X5 X6 : G) :
      (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇
      X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇
      (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)))) := by
    first | exact superpose ef706 ef2297 | exact superpose ef2297 ef706
  have ef2381 (X0 X1 X2 X3 X4 X5 X6 : G) :
      (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0) := by
    first | exact superpose ef7 ef2356 | exact superpose ef2356 ef7
  have ef2398 (X0 X1 X2 X3 X4 X5 X6 : G) :
      X0 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0)) ◇ X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0) := by
    first | exact superpose ef845 ef2381 | exact superpose ef2381 ef845
  have ef2413 (X0 X1 X2 X3 X4 X5 X6 : G) :
      X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X0) = (X6 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) ◇
      ((X1 ◇ (X2 ◇ X3)) ◇ X0) := by
    first | exact superpose ef8 ef2398 | exact superpose ef2398 ef8
  have ef2577 (X0 X1 X2 X3 X4 : G) :
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) = X4 ◇
      ((((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)))) ◇
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0))) := by
    first | exact superpose ef37 ef25 | exact superpose ef25 ef37
  have ef2625 (X0 X1 X2 X3 X4 : G) :
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) = X4 ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0) ◇ ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0))) ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0))) := by
    first | exact superpose ef850 ef2577 | exact superpose ef2577 ef850
  have ef2679 (X0 X1 X2 X3 X4 : G) :
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇
      X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) = X4 ◇ (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) ◇
      ((((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0))) := by
    first | exact superpose ef844 ef2625 | exact superpose ef2625 ef844
  have ef2718 (X0 X1 X2 X3 X4 : G) :
      (X0 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) = X4 ◇
      (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) ◇
      (X0 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ X0))) := by
    first | exact superpose ef2413 ef2679 | exact superpose ef2679 ef2413
  have ef2739 (X0 X1 X2 X3 X4 : G) :
      X4 ◇ X0 = (X0 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) := by
    first | exact superpose ef123 ef2718 | exact superpose ef2718 ef123
  have ef2756 (X0 X1 X2 X3 X4 : G) :
      X4 ◇ X0 = (X0 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ X0)) ◇ X0)) ◇
      (((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0))) := by
    first | exact superpose ef706 ef2739 | exact superpose ef2739 ef706
  have ef2773 (X0 X1 X2 X3 X4 : G) : X4 ◇ X0 = (X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0 := by
    first | exact superpose ef7 ef2756 | exact superpose ef2756 ef7
  have ef2962 (X0 X1 X2 X3 X4 X5 X6 : G) :
      ((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0) ◇ (X0 ◇
      ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) = (X2 ◇ (X6 ◇ X2)) ◇
      ((((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0))) ◇
      ((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0)) := by
    first | exact superpose ef21 ef20 | exact superpose ef20 ef21
  have ef3077 (X0 X1 X2 X3 X4 X5 X6 : G) :
      ((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) = (X2 ◇ (X6 ◇ X2)) ◇
      (X0 ◇ ((X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0)) ◇ X0)) := by
    first | exact superpose ef2413 ef2962 | exact superpose ef2962 ef2413
  have ef3146 (X0 X1 X2 X3 X4 X5 X6 : G) :
      ((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0) ◇
      (X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) = (X2 ◇ (X6 ◇ X2)) ◇
      (X0 ◇ ((X0 ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X2))) ◇ X0)) ◇ X0)) := by
    first | exact superpose ef8 ef3077 | exact superpose ef3077 ef8
  have ef3177 (X0 X2 X6 : G) :
      ((X0 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X6 ◇ X2)) ◇
      (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := by
    first | exact superpose ef2773 ef3146 | exact superpose ef3146 ef2773
  have ef3199 (X0 X2 X6 : G) :
      (X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X6 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := by
    first | exact superpose ef706 ef3177 | exact superpose ef3177 ef706
  have ef3266 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X2 = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X2 := by
    first | exact superpose ef25 ef2773 | exact superpose ef2773 ef25
  have ef3383 :
      x ≠ ((((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ y)) ◇ x))) ◇ ((x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ y)) ◇ x)))) ◇ (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      ((x ◇ (x ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x)))) ◇
      (x ◇ ((x ◇ (x ◇ y)) ◇ x))))) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2773 ef744 | exact superpose ef744 ef2773
  have ef3557 :
      x ≠ (x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2773 ef3383 | exact superpose ef3383 ef2773
  have ef3623 :
      x ≠ (x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇
      (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef3266 ef3557 | exact superpose ef3557 ef3266
  have ef3645 :
      x ≠ (x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (x ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ x))))) := by
    first | exact superpose ef3199 ef3623 | exact superpose ef3623 ef3199
  have ef3663 : x ≠ (x ◇ ((x ◇ (x ◇ y)) ◇ x)) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef5 ef3645 | exact superpose ef3645 ef5
  subsumption ef3663 ef7

theorem Equation1478_termStructuralFrom_Equation690 :
    Law1478.TermStructuralFrom Law690 := by
  intro G M hGL
  have h : Equation690 G := Law690.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op y (M.op y x))) (M.op (M.op (M.op x x) (M.op x y)) y))⟩, ?_, ?_, ?_⟩
  · rw [@Law1478.models_iff]
    exact fun x y ↦ @aux690_1478 G M h x y
  · exact ⟨(tm (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))) (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 1) (Term.var 1))), funext fun z ↦ (@inv690_c343535e G M h (z 0) (z 1)).symm⟩

/-- Equation 1525 `x = (y ◇ y) ◇ (y ◇ (x ◇ x))` holds of the term
`x □ y := (((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)` over any magma
satisfying equation 690 `x = y ◇ (x ◇ ((z ◇ y) ◇ x))`. -/
private theorem aux690_1525 [Magma G] (h : Equation690 G) (x y : G) :
    x = (((((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)))) ◇ (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ (((y ◇ y) ◇
      (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      (((y ◇ y) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y))))) ◇
      (((((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      (((y ◇ y) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))))) ◇ ((((y ◇ y) ◇ (y ◇
      y)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ (((y ◇ y) ◇ (y ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)))) ◇ (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ (((y ◇ y) ◇
      (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      (((y ◇ y) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y))))) ◇
      (((((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      (((y ◇ y) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))))) ◇ ((((y ◇ y) ◇ (y ◇
      y)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ (((y ◇ y) ◇ (y ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0) = X1 ◇ ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X0) := superpose ef5 ef5
  have ef11 (X0 X1 X4 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) = X4 := superpose ef7 ef7
  have ef18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)) = X2 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef20 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X1) = (X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef25 (X0 X1 : G) :
      (X0 ◇ (X1 ◇ X0)) ◇ X0 = X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef123 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef11 ef23 | exact superpose ef23 ef11
  have ef124 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X0 ◇ (X2 ◇ X0)) ◇ X0 := by
    first | exact superpose ef11 ef18 | exact superpose ef18 ef11
  have ef220 (X0 X1 X2 X3 : G) : (X3 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef123 | exact superpose ef123 ef8
  have ef298 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1) := by
    first | exact superpose ef31 ef5 | exact superpose ef5 ef31
  have ef305 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X2 ◇ (X3 ◇ X0)) ◇ X0 := by
    first | exact superpose ef31 ef18 | exact superpose ef18 ef31
  have ef400 (X0 X1 X2 X3 : G) : X0 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef23 | exact superpose ef23 ef124
  have ef496 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X2 ◇ X3) ◇ X0) = (X3 ◇ (X4 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef20 | exact superpose ef20 ef124
  have ef548 (X0 X2 X3 X4 : G) : X0 ◇ ((X4 ◇ X3) ◇ X0) = X0 ◇ ((X2 ◇ X3) ◇ X0) := by
    first | exact superpose ef400 ef496 | exact superpose ef496 ef400
  have ef601 (X0 X1 X2 X3 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇
      (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef18 ef305 | exact superpose ef305 ef18
  have ef627 (X0 X1 X2 X3 X4 : G) : X2 ◇ (X3 ◇ X2) = (X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2) := by
    first | exact superpose ef305 ef23 | exact superpose ef23 ef305
  have ef704 (X0 X1 X3 : G) : (X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef601 | exact superpose ef601 ef298
  have ef778 (X0 X1 X2 : G) :
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef25 ef23 | exact superpose ef23 ef25
  have ef802 (X0 X1 X2 : G) :
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef704 ef778 | exact superpose ef778 ef704
  have ef822 (X0 X1 X2 : G) :
      X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef400 ef802 | exact superpose ef802 ef400
  have ef838 (X0 X1 X2 : G) : X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇ (X1 ◇ X0) := by
    first | exact superpose ef7 ef822 | exact superpose ef822 ef7
  have ef1251 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X1) := by
    first | exact superpose ef18 ef548 | exact superpose ef548 ef18
  have ef2987 :
      x ≠ (((((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)))) ◇ (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇ (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y))))) ◇
      (((((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))))) ◇ ((((y ◇ y) ◇ (y ◇
      y)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ ((((x ◇ x) ◇
      (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef298 ef6 | exact superpose ef6 ef298
  have ef2989 (X0 X1 X2 X3 X4 : G) :
      X4 ◇ (X0 ◇ (X1 ◇ X0)) = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef8 | exact superpose ef8 ef298
  have ef2996 (X0 X1 X2 X3 : G) : (X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)) = (X3 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef23 | exact superpose ef23 ef298
  have ef3073 :
      x ≠ ((((y ◇ y) ◇ (y ◇ y)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ ((((x ◇
      x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇ (((((y ◇ y) ◇ (y ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)))) ◇ ((((y ◇ y) ◇ (y ◇
      y)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇ ((((x ◇ x) ◇
      (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef627 ef2987 | exact superpose ef2987 ef627
  have ef3086 :
      x ≠ ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇ (((((x ◇ x) ◇
      (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2989 ef3073 | exact superpose ef3073 ef2989
  have ef3089 :
      x ≠ ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ y) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2989 ef3086 | exact superpose ef3086 ef2989
  have ef3091 :
      x ≠ ((((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ (y ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ y)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2996 ef3089 | exact superpose ef3089 ef2996
  have ef3093 :
      x ≠ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇ y) ◇ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2996 ef3091 | exact superpose ef3091 ef2996
  have ef3095 :
      x ≠ (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ y) ◇
      (y ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef1251 ef3093 | exact superpose ef3093 ef1251
  have ef3097 : x ≠ (y ◇ x) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇ y) ◇ (y ◇ x)) := by
    first | exact superpose ef220 ef3095 | exact superpose ef3095 ef220
  have ef3099 : x ≠ (y ◇ x) ◇ (x ◇ ((x ◇ (y ◇ x)) ◇ x)) := by
    first | exact superpose ef838 ef3097 | exact superpose ef3097 ef838
  subsumption ef3099 ef5

theorem Equation1525_termStructuralFrom_Equation690 :
    Law1525.TermStructuralFrom Law690 := by
  intro G M hGL
  have h : Equation690 G := Law690.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op y (M.op y x))) (M.op (M.op (M.op x x) (M.op x y)) y))⟩, ?_, ?_, ?_⟩
  · rw [@Law1525.models_iff]
    exact fun x y ↦ @aux690_1525 G M h x y
  · exact ⟨(tm (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))) (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 1) (Term.var 1))), funext fun z ↦ (@inv690_c343535e G M h (z 0) (z 1)).symm⟩

/-- Equation 1586 `x = (y ◇ z) ◇ (z ◇ (x ◇ x))` holds of the term
`x □ y := (((x ◇ x) ◇ (x ◇ x)) ◇ (y ◇ (y ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ y)) ◇ y)` over any magma
satisfying equation 690 `x = y ◇ (x ◇ ((z ◇ y) ◇ x))`. -/
private theorem aux690_1586 [Magma G] (h : Equation690 G) (x y z : G) :
    x = (((((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)))) ◇ (((((z ◇ z) ◇ (z ◇ z)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇ (((z ◇ z) ◇
      (z ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      (((((z ◇ z) ◇ (z ◇ z)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇
      (((z ◇ z) ◇ (z ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z))))) ◇
      (((((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇ ((((z ◇ z) ◇ (z ◇ z)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇
      (((z ◇ z) ◇ (z ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))))) ◇ ((((z ◇ z) ◇ (z ◇
      z)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇ (((z ◇ z) ◇ (z ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ (((((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)))) ◇ (((((z ◇ z) ◇ (z ◇ z)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇ (((z ◇ z) ◇
      (z ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      (((((z ◇ z) ◇ (z ◇ z)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇
      (((z ◇ z) ◇ (z ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z))))) ◇
      (((((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇ ((((z ◇ z) ◇ (z ◇ z)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇
      (((z ◇ z) ◇ (z ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))))) ◇ ((((z ◇ z) ◇ (z ◇
      z)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇ (((z ◇ z) ◇ (z ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3)) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 X3 : G) :
      X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0) = X1 ◇ ((X0 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X0) := superpose ef5 ef5
  have ef11 (X0 X1 X4 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X4)) = X4 := superpose ef7 ef7
  have ef18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X2)) = X2 := by
    first | exact superpose ef7 ef5 | exact superpose ef5 ef7
  have ef20 (X0 X1 X2 X3 : G) :
      X1 ◇ ((X2 ◇ X0) ◇ X1) = (X0 ◇ (X3 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef25 (X0 X1 : G) :
      (X0 ◇ (X1 ◇ X0)) ◇ X0 = X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef31 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef123 (X0 X1 X2 : G) : (X2 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef11 ef23 | exact superpose ef23 ef11
  have ef124 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X0 ◇ (X2 ◇ X0)) ◇ X0 := by
    first | exact superpose ef11 ef18 | exact superpose ef18 ef11
  have ef220 (X0 X1 X2 X3 : G) : (X3 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef123 | exact superpose ef123 ef8
  have ef298 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1) := by
    first | exact superpose ef31 ef5 | exact superpose ef5 ef31
  have ef305 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X0 = (X2 ◇ (X3 ◇ X0)) ◇ X0 := by
    first | exact superpose ef31 ef18 | exact superpose ef18 ef31
  have ef400 (X0 X1 X2 X3 : G) : X0 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef23 | exact superpose ef23 ef124
  have ef496 (X0 X1 X2 X3 X4 : G) :
      X0 ◇ ((X2 ◇ X3) ◇ X0) = (X3 ◇ (X4 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    first | exact superpose ef124 ef20 | exact superpose ef20 ef124
  have ef548 (X0 X2 X3 X4 : G) : X0 ◇ ((X4 ◇ X3) ◇ X0) = X0 ◇ ((X2 ◇ X3) ◇ X0) := by
    first | exact superpose ef400 ef496 | exact superpose ef496 ef400
  have ef601 (X0 X1 X2 X3 : G) :
      ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇
      (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef18 ef305 | exact superpose ef305 ef18
  have ef627 (X0 X1 X2 X3 X4 : G) : X2 ◇ (X3 ◇ X2) = (X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2) := by
    first | exact superpose ef305 ef23 | exact superpose ef23 ef305
  have ef704 (X0 X1 X3 : G) : (X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) = (X3 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef601 | exact superpose ef601 ef298
  have ef778 (X0 X1 X2 : G) :
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef25 ef23 | exact superpose ef23 ef25
  have ef802 (X0 X1 X2 : G) :
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇
      ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef704 ef778 | exact superpose ef778 ef704
  have ef822 (X0 X1 X2 : G) :
      X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇
      ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    first | exact superpose ef400 ef802 | exact superpose ef802 ef400
  have ef838 (X0 X1 X2 : G) : X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X2 ◇ X1) ◇ (X1 ◇ X0) := by
    first | exact superpose ef7 ef822 | exact superpose ef822 ef7
  have ef1251 (X0 X1 X2 X3 : G) : X1 ◇ (X0 ◇ X1) = X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X1) := by
    first | exact superpose ef18 ef548 | exact superpose ef548 ef18
  have ef2987 :
      x ≠ (((((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇ ((((y ◇ y) ◇ (y ◇ y)) ◇
      (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)))) ◇ (((((z ◇ z) ◇ (z ◇ z)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇ (((((z ◇ z) ◇ (z ◇ z)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z))))) ◇
      (((((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z))) ◇
      (((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇ ((((z ◇ z) ◇ (z ◇ z)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))))) ◇ ((((z ◇ z) ◇ (z ◇
      z)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇ ((((x ◇ x) ◇
      (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef298 ef6 | exact superpose ef6 ef298
  have ef2989 (X0 X1 X2 X3 X4 : G) :
      X4 ◇ (X0 ◇ (X1 ◇ X0)) = (X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef8 | exact superpose ef8 ef298
  have ef2996 (X0 X1 X2 X3 : G) : (X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)) = (X3 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0)) := by
    first | exact superpose ef298 ef23 | exact superpose ef23 ef298
  have ef3073 :
      x ≠ ((((z ◇ z) ◇ (z ◇ z)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇ ((((x ◇
      x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((((z ◇ z) ◇ (z ◇ z)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇ (((((z ◇ z) ◇ (z ◇ z)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)))) ◇ ((((z ◇ z) ◇ (z ◇
      z)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇ ((((x ◇ x) ◇
      (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef627 ef2987 | exact superpose ef2987 ef627
  have ef3086 :
      x ≠ ((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇ (((((x ◇ x) ◇
      (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇
      ((((z ◇ z) ◇ (z ◇ z)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2989 ef3073 | exact superpose ef3073 ef2989
  have ef3089 :
      x ≠ ((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇ z) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2989 ef3086 | exact superpose ef3086 ef2989
  have ef3091 :
      x ≠ ((((y ◇ y) ◇ (y ◇ y)) ◇ (z ◇ (z ◇ y))) ◇ (((y ◇ y) ◇ (y ◇ z)) ◇ z)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ (z ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2996 ef3089 | exact superpose ef3089 ef2996
  have ef3093 :
      x ≠ (z ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇ ((((y ◇ y) ◇ (y ◇ z)) ◇ z) ◇ (z ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef2996 ef3091 | exact superpose ef3091 ef2996
  have ef3095 :
      x ≠ (z ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)))) ◇
      ((((y ◇ y) ◇ (y ◇ z)) ◇ z) ◇
      (z ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))))) := by
    first | exact superpose ef1251 ef3093 | exact superpose ef3093 ef1251
  have ef3097 : x ≠ (z ◇ x) ◇ ((((y ◇ y) ◇ (y ◇ z)) ◇ z) ◇ (z ◇ x)) := by
    first | exact superpose ef220 ef3095 | exact superpose ef3095 ef220
  have ef3099 : x ≠ (z ◇ x) ◇ (x ◇ ((x ◇ (z ◇ x)) ◇ x)) := by
    first | exact superpose ef838 ef3097 | exact superpose ef3097 ef838
  subsumption ef3099 ef5

theorem Equation1586_termStructuralFrom_Equation690 :
    Law1586.TermStructuralFrom Law690 := by
  intro G M hGL
  have h : Equation690 G := Law690.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op y (M.op y x))) (M.op (M.op (M.op x x) (M.op x y)) y))⟩, ?_, ?_, ?_⟩
  · rw [@Law1586.models_iff]
    exact fun x y z ↦ @aux690_1586 G M h x y z
  · exact ⟨(tm (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (tm (Term.var 1) (tm (Term.var 1) (Term.var 0)))) (tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 1))) (Term.var 1))), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 1) (Term.var 1))), funext fun z ↦ (@inv690_c343535e G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := ((x ◇ x) ◇ x) ◇ y` of equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))` can
be undone: the operation is recovered as `x ◇ y = (x ◇ (x ◇ x)) ◇ y` read in `□`. -/
private theorem inv695_c30761ea [Magma G] (h : Equation695 G) (x y : G) :
    (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ y = x ◇ y := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      (((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ y ≠ x ◇ y := mod_symm nh
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ X1 = (X0 ◇ X0) ◇ (X2 ◇ X2) := superpose ef8 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef16 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef60 (X0 X1 : G) :
      x ◇ y ≠ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ y := by
    first | exact superpose ef10 ef6 | exact superpose ef6 ef10
  have ef221 (X0 X1 X2 : G) :
      x ◇ y ≠ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X0) ◇ x) ◇ (((X0 ◇ X0) ◇ x) ◇ x))) ◇ y := by
    first | exact superpose ef15 ef60 | exact superpose ef60 ef15
  have ef313 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef16 ef5 | exact superpose ef5 ef16
  have ef445 (X0 X1 X2 X3 : G) :
      x ◇ y ≠ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X3 ◇ X3) ◇ x) ◇ (((X3 ◇ X3) ◇ x) ◇ x))) ◇
      y := by
    first | exact superpose ef15 ef221 | exact superpose ef221 ef15
  have ef469 (X0 X1 X2 X3 : G) :
      x ◇ y ≠ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X3 ◇ X3) ◇ x)) ◇ y := by
    first | exact superpose ef313 ef445 | exact superpose ef445 ef313
  have ef477 (X1 X3 : G) : x ◇ y ≠ ((X1 ◇ X1) ◇ ((X3 ◇ X3) ◇ x)) ◇ y := by
    first | exact superpose ef16 ef469 | exact superpose ef469 ef16
  have ef485 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef16 ef477 | exact superpose ef477 ef16
  exact absurd rfl ef485

/-- Equation 417 `x = x ◇ (x ◇ (y ◇ (x ◇ y)))` holds of the term `x □ y := ((x ◇ x) ◇ x) ◇ y` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_417 [Magma G] (h : Equation695 G) (x y : G) :
    x = ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X0) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef14 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef35 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3) = X2 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef159 (X0 : G) :
      x ≠ ((X0 ◇ X0) ◇ x) ◇ (((X0 ◇ X0) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ (((X0 ◇ X0) ◇ x) ◇ y))) := by
    first | exact superpose ef14 ef6 | exact superpose ef6 ef14
  have ef176 (X0 X1 : G) :
      x ≠ ((X1 ◇ X1) ◇ x) ◇ (((X1 ◇ X1) ◇ x) ◇ (((X0 ◇ X0) ◇ y) ◇ (((X1 ◇ X1) ◇ x) ◇ y))) := by
    first | exact superpose ef14 ef159 | exact superpose ef159 ef14
  have ef235 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef15 ef5 | exact superpose ef5 ef15
  have ef327 (X0 X1 X2 : G) :
      x ≠ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ x) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ x) ◇
      (((X2 ◇ X2) ◇ y) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ x) ◇ y))) := by
    first | exact superpose ef14 ef176 | exact superpose ef176 ef14
  have ef330 (X0 X1 : G) :
      x ≠ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ x) ◇
      ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ x) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ x)) := by
    first | exact superpose ef235 ef327 | exact superpose ef327 ef235
  subsumption ef330 ef35

theorem Equation417_termStructuralFrom_Equation695 :
    Law417.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law417.models_iff]
    exact fun x y ↦ @aux695_417 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv695_c30761ea G M h (z 0) (z 1)).symm⟩

/-- Equation 429 `x = x ◇ (y ◇ (x ◇ (y ◇ x)))` holds of the term `x □ y := ((x ◇ x) ◇ x) ◇ y` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_429 [Magma G] (h : Equation695 G) (x y : G) :
    x = ((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ x))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ x))) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef14 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef160 (X0 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇ (((X0 ◇ X0) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (((X0 ◇ X0) ◇ y) ◇ x))) := by
    first | exact superpose ef14 ef6 | exact superpose ef6 ef14
  have ef235 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef15 ef5 | exact superpose ef5 ef15
  have ef247 (X0 X1 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇
      ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y) ◇ x))) := by
    first | exact superpose ef14 ef160 | exact superpose ef160 ef14
  have ef250 (X0 X1 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y)) := by
    first | exact superpose ef235 ef247 | exact superpose ef247 ef235
  subsumption ef250 ef8

theorem Equation429_termStructuralFrom_Equation695 :
    Law429.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law429.models_iff]
    exact fun x y ↦ @aux695_429 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv695_c30761ea G M h (z 0) (z 1)).symm⟩

/-- Equation 440 `x = x ◇ (y ◇ (y ◇ (y ◇ y)))` holds of the term `x □ y := ((x ◇ x) ◇ x) ◇ y` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_440 [Magma G] (h : Equation695 G) (x y : G) :
    x = ((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X0) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef14 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef35 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3) = X2 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef159 (X0 : G) :
      x ≠ ((X0 ◇ X0) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) := by
    first | exact superpose ef14 ef6 | exact superpose ef6 ef14
  have ef184 (X0 X1 : G) :
      x ≠ ((X1 ◇ X1) ◇ x) ◇ (((X0 ◇ X0) ◇ y) ◇ (((X0 ◇ X0) ◇ y) ◇ (((X0 ◇ X0) ◇ y) ◇ y))) := by
    first | exact superpose ef14 ef159 | exact superpose ef159 ef14
  have ef235 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef15 ef5 | exact superpose ef5 ef15
  have ef317 (X0 X1 X2 : G) :
      x ≠ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ x) ◇
      (((X2 ◇ X2) ◇ y) ◇ (((X2 ◇ X2) ◇ y) ◇ (((X2 ◇ X2) ◇ y) ◇ y))) := by
    first | exact superpose ef14 ef184 | exact superpose ef184 ef14
  have ef330 (X0 X1 X2 : G) :
      x ≠ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ x) ◇ (((X2 ◇ X2) ◇ y) ◇ ((X2 ◇ X2) ◇ y)) := by
    first | exact superpose ef235 ef317 | exact superpose ef317 ef235
  subsumption ef330 ef35

theorem Equation440_termStructuralFrom_Equation695 :
    Law440.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law440.models_iff]
    exact fun x y ↦ @aux695_440 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv695_c30761ea G M h (z 0) (z 1)).symm⟩

/-- Equation 452 `x = x ◇ (y ◇ (z ◇ (y ◇ z)))` holds of the term `x □ y := ((x ◇ x) ◇ x) ◇ y` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_452 [Magma G] (h : Equation695 G) (x y z : G) :
    x = ((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ (((z ◇ z) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z))) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ (((z ◇ z) ◇ z) ◇ (((y ◇ y) ◇ y) ◇ z))) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef14 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef161 (X0 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇ (((X0 ◇ X0) ◇ y) ◇ (((z ◇ z) ◇ z) ◇ (((X0 ◇ X0) ◇ y) ◇ z))) := by
    first | exact superpose ef14 ef6 | exact superpose ef6 ef14
  have ef239 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef15 ef5 | exact superpose ef5 ef15
  have ef253 (X0 X1 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇
      ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y) ◇ (((z ◇ z) ◇ z) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y) ◇ z))) := by
    first | exact superpose ef14 ef161 | exact superpose ef161 ef14
  have ef256 (X0 X1 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y)) := by
    first | exact superpose ef239 ef253 | exact superpose ef253 ef239
  subsumption ef256 ef8

theorem Equation452_termStructuralFrom_Equation695 :
    Law452.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law452.models_iff]
    exact fun x y z ↦ @aux695_452 G M h x y z
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv695_c30761ea G M h (z 0) (z 1)).symm⟩

/-- Equation 1020 `x = x ◇ ((x ◇ (x ◇ x)) ◇ x)` holds of the term `x □ y := ((x ◇ x) ◇ x) ◇ y` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_1020 [Magma G] (h : Equation695 G) (x : G) :
    x = ((x ◇ x) ◇ x) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ x) ◇ x) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ X1 = (X0 ◇ X0) ◇ (X2 ◇ X2) := superpose ef8 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef16 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef60 (X0 X1 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇
      ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ x) := by
    first | exact superpose ef10 ef6 | exact superpose ef6 ef10
  have ef219 (X0 X1 X2 : G) :
      x ≠ ((X0 ◇ X0) ◇ x) ◇
      ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X0) ◇ x) ◇ (((X0 ◇ X0) ◇ x) ◇ x))) ◇ x) := by
    first | exact superpose ef15 ef60 | exact superpose ef60 ef15
  have ef313 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef16 ef5 | exact superpose ef5 ef16
  have ef445 (X0 X1 X2 X3 : G) :
      x ≠ ((X2 ◇ X2) ◇ x) ◇
      ((((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X2 ◇ X2) ◇ x) ◇ (((X2 ◇ X2) ◇ x) ◇ x))) ◇
      x) := by
    first | exact superpose ef15 ef219 | exact superpose ef219 ef15
  have ef469 (X0 X1 X2 X3 : G) :
      x ≠ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ (((X2 ◇ X2) ◇ x) ◇ (((X2 ◇ X2) ◇ x) ◇ x)) := by
    first | exact superpose ef313 ef445 | exact superpose ef445 ef313
  have ef477 (X0 X1 X2 X3 : G) : x ≠ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X2 ◇ X2) ◇ x) := by
    first | exact superpose ef313 ef469 | exact superpose ef469 ef313
  have ef485 (X1 X2 : G) : x ≠ (X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ x) := by
    first | exact superpose ef16 ef477 | exact superpose ef477 ef16
  subsumption ef485 ef16

theorem Equation1020_termStructuralFrom_Equation695 :
    Law1020.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1020.models_iff]
    exact fun x ↦ @aux695_1020 G M h x
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv695_c30761ea G M h (z 0) (z 1)).symm⟩

/-- Equation 1026 `x = x ◇ ((x ◇ (y ◇ x)) ◇ y)` holds of the term `x □ y := ((x ◇ x) ◇ x) ◇ y` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_1026 [Magma G] (h : Equation695 G) (x y : G) :
    x = ((x ◇ x) ◇ x) ◇
      ((((((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ x))) ◇
      (((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ x))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ x) ◇ x) ◇
      ((((((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ x))) ◇
      (((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ x))) ◇ y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ X1 = (X0 ◇ X0) ◇ (X2 ◇ X2) := superpose ef8 ef8
  have ef14 (X0 X1 X2 : G) : (X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0)) = X2 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef16 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef68 (X0 X1 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇
      ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ x))) ◇ y) := by
    first | exact superpose ef10 ef6 | exact superpose ef6 ef10
  have ef145 (X0 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇ (((X0 ◇ X0) ◇ (((x ◇ x) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ x))) ◇ y) := by
    first | exact superpose ef14 ef68 | exact superpose ef68 ef14
  have ef272 (X0 X1 : G) :
      x ≠ ((X0 ◇ X0) ◇ x) ◇ (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ x) ◇ (((y ◇ y) ◇ y) ◇ x))) ◇ y) := by
    first | exact superpose ef15 ef145 | exact superpose ef145 ef15
  have ef319 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef16 ef5 | exact superpose ef5 ef16
  have ef361 (X0 X1 X2 : G) :
      x ≠ ((X1 ◇ X1) ◇ x) ◇ (((X2 ◇ X2) ◇ (((X1 ◇ X1) ◇ x) ◇ (((X0 ◇ X0) ◇ y) ◇ x))) ◇ y) := by
    first | exact superpose ef15 ef272 | exact superpose ef272 ef15
  have ef364 (X0 X1 X2 : G) : x ≠ ((X1 ◇ X1) ◇ x) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ y)) ◇ y) := by
    first | exact superpose ef319 ef361 | exact superpose ef361 ef319
  have ef366 (X1 : G) : x ≠ ((X1 ◇ X1) ◇ x) ◇ (y ◇ y) := by
    first | exact superpose ef16 ef364 | exact superpose ef364 ef16
  subsumption ef366 ef8

theorem Equation1026_termStructuralFrom_Equation695 :
    Law1026.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1026.models_iff]
    exact fun x y ↦ @aux695_1026 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv695_c30761ea G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := ((x ◇ x) ◇ y) ◇ x` of equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))` can
be undone: the operation is recovered as `x ◇ y = y ◇ ((x ◇ x) ◇ x)` read in `□`. -/
private theorem inv695_342f8883 [Magma G] (h : Equation695 G) (x y : G) :
    ((y ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ y = x ◇
      y := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      ((y ◇ y) ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      y ≠ x ◇ y := mod_symm nh
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ X1 = (X0 ◇ X0) ◇ (X2 ◇ X2) := superpose ef8 ef8
  have ef14 (X0 X1 X2 : G) : (X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0)) = X2 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef16 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef73 (X0 X1 : G) :
      x ◇ y ≠ ((y ◇ y) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ y := by
    first | exact superpose ef10 ef6 | exact superpose ef6 ef10
  have ef145 (X0 : G) : x ◇ y ≠ ((y ◇ y) ◇ (((X0 ◇ X0) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ y := by
    first | exact superpose ef14 ef73 | exact superpose ef73 ef14
  have ef274 (X0 X1 : G) : x ◇ y ≠ ((y ◇ y) ◇ (((X1 ◇ X1) ◇ x) ◇ (((X0 ◇ X0) ◇ x) ◇ x))) ◇ y := by
    first | exact superpose ef15 ef145 | exact superpose ef145 ef15
  have ef317 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef16 ef5 | exact superpose ef5 ef16
  have ef363 (X0 X1 X2 : G) :
      x ◇ y ≠ ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ x) ◇ (((X2 ◇ X2) ◇ x) ◇ x))) ◇ y := by
    first | exact superpose ef15 ef274 | exact superpose ef274 ef15
  have ef364 (X0 X2 : G) : x ◇ y ≠ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ x)) ◇ y := by
    first | exact superpose ef317 ef363 | exact superpose ef363 ef317
  have ef370 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef16 ef364 | exact superpose ef364 ef16
  exact absurd rfl ef370

/-- Equation 1036 `x = x ◇ ((y ◇ (x ◇ x)) ◇ y)` holds of the term `x □ y := ((x ◇ x) ◇ y) ◇ x` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_1036 [Magma G] (h : Equation695 G) (x y : G) :
    x = ((x ◇ x) ◇
      ((((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y)) ◇ y) ◇
      (((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y))) ◇ x := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ x) ◇
      ((((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y)) ◇ y) ◇
      (((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y))) ◇ x := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X0) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ X1 = (X0 ◇ X0) ◇ (X2 ◇ X2) := superpose ef8 ef8
  have ef11 (X0 X1 X2 X3 : G) : X0 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)) = X0 ◇ (X3 ◇ X3) := by
    first | exact superpose ef5 ef8 | exact superpose ef8 ef5
  have ef14 (X0 X1 X2 : G) : (X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0)) = X2 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef16 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef22 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X1) = X3 := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef28 (X0 X1 X2 X3 X4 : G) :
      ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X3 ◇ X3) ◇ (X4 ◇ X4))) ◇ X0 = X2 := by
    first | exact superpose ef5 ef7 | exact superpose ef7 ef5
  have ef30 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X4 ◇ X4) ◇ (X5 ◇ X5)) = ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) ◇ X0 := superpose ef7 ef7
  have ef73 (X0 X1 : G) :
      x ≠ ((x ◇ x) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y))) ◇
      x := by
    first | exact superpose ef10 ef6 | exact superpose ef6 ef10
  have ef145 (X0 : G) :
      x ≠ ((x ◇ x) ◇ (((X0 ◇ X0) ◇ y) ◇ (((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ y))) ◇ x := by
    first | exact superpose ef14 ef73 | exact superpose ef73 ef14
  have ef278 (X0 X1 : G) :
      x ≠ ((x ◇ x) ◇ (((X1 ◇ X1) ◇ y) ◇ (((y ◇ y) ◇ (((X0 ◇ X0) ◇ x) ◇ x)) ◇ y))) ◇ x := by
    first | exact superpose ef15 ef145 | exact superpose ef145 ef15
  have ef323 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef16 ef5 | exact superpose ef5 ef16
  have ef365 (X0 X1 X2 : G) :
      x ≠ ((x ◇ x) ◇ (((X2 ◇ X2) ◇ y) ◇ (((y ◇ y) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ x) ◇ x)) ◇ y))) ◇
      x := by
    first | exact superpose ef15 ef278 | exact superpose ef278 ef15
  have ef376 (X0 X1 : G) : x ≠ ((x ◇ x) ◇ ((y ◇ y) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ x) ◇ x))) ◇ x := by
    first | exact superpose ef323 ef365 | exact superpose ef365 ef323
  have ef384 (X0 X1 : G) : x ≠ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ x) ◇ x) ◇ x := by
    first | exact superpose ef16 ef376 | exact superpose ef376 ef16
  have ef1597 (X0 X1 X2 X3 X4 X5 : G) :
      (X1 ◇ ((X3 ◇ X3) ◇ X0)) ◇ ((X4 ◇ X4) ◇ (X5 ◇ X5)) = (X1 ◇ (X2 ◇ X2)) ◇ X0 := by
    first | exact superpose ef28 ef22 | exact superpose ef22 ef28
  have ef2002 (X0 X1 : G) : x ≠ ((x ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ x) ◇ x := by
    first | exact superpose ef30 ef384 | exact superpose ef384 ef30
  have ef2298 (X0 : G) : x ≠ ((x ◇ (X0 ◇ X0)) ◇ x) ◇ x := by
    first | exact superpose ef11 ef2002 | exact superpose ef2002 ef11
  have ef47886 (X0 X1 X2 : G) : x ≠ ((x ◇ ((X0 ◇ X0) ◇ x)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ x := by
    first | exact superpose ef1597 ef2298 | exact superpose ef2298 ef1597
  subsumption ef47886 ef28

theorem Equation1036_termStructuralFrom_Equation695 :
    Law1036.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law1036.models_iff]
    exact fun x y ↦ @aux695_1036 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0))), funext fun z ↦ (@inv695_342f8883 G M h (z 0) (z 1)).symm⟩

/-- Equation 1038 `x = x ◇ ((y ◇ (x ◇ y)) ◇ x)` holds of the term `x □ y := ((x ◇ x) ◇ x) ◇ y` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_1038 [Magma G] (h : Equation695 G) (x y : G) :
    x = ((x ◇ x) ◇ x) ◇
      ((((((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ x) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ x) ◇ x) ◇
      ((((((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ x) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ X1 = (X0 ◇ X0) ◇ (X2 ◇ X2) := superpose ef8 ef8
  have ef14 (X0 X1 X2 : G) : (X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0)) = X2 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef16 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef68 (X0 X1 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇
      ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ x) := by
    first | exact superpose ef10 ef6 | exact superpose ef6 ef10
  have ef145 (X0 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇ (((X0 ◇ X0) ◇ (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ x) := by
    first | exact superpose ef14 ef68 | exact superpose ef68 ef14
  have ef272 (X0 X1 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇ (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ x) := by
    first | exact superpose ef15 ef145 | exact superpose ef145 ef15
  have ef319 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef16 ef5 | exact superpose ef5 ef16
  have ef361 (X0 X1 X2 : G) :
      x ≠ ((X0 ◇ X0) ◇ x) ◇ (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ y) ◇ (((X0 ◇ X0) ◇ x) ◇ y))) ◇ x) := by
    first | exact superpose ef15 ef272 | exact superpose ef272 ef15
  have ef364 (X0 X1 X2 : G) : x ≠ (X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ y) ◇ (((X0 ◇ X0) ◇ x) ◇ y)) := by
    first | exact superpose ef319 ef361 | exact superpose ef361 ef319
  have ef370 (X0 X1 : G) : x ≠ (X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ x) := by
    first | exact superpose ef319 ef364 | exact superpose ef364 ef319
  subsumption ef370 ef16

theorem Equation1038_termStructuralFrom_Equation695 :
    Law1038.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1038.models_iff]
    exact fun x y ↦ @aux695_1038 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv695_c30761ea G M h (z 0) (z 1)).symm⟩

/-- Equation 1049 `x = x ◇ ((y ◇ (y ◇ y)) ◇ y)` holds of the term `x □ y := ((x ◇ x) ◇ x) ◇ y` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_1049 [Magma G] (h : Equation695 G) (x y : G) :
    x = ((x ◇ x) ◇ x) ◇
      ((((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ x) ◇ x) ◇
      ((((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef14 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef159 (X0 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇ (((X0 ◇ X0) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) := by
    first | exact superpose ef14 ef6 | exact superpose ef6 ef14
  have ef179 (X0 X1 : G) :
      x ≠ ((X0 ◇ X0) ◇ x) ◇ (((X1 ◇ X1) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ y) := by
    first | exact superpose ef14 ef159 | exact superpose ef159 ef14
  have ef240 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef15 ef5 | exact superpose ef5 ef15
  have ef261 (X0 X1 X2 : G) :
      x ≠ ((X1 ◇ X1) ◇ x) ◇ (((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ y) ◇ (((X0 ◇ X0) ◇ y) ◇ y))) ◇ y) := by
    first | exact superpose ef14 ef179 | exact superpose ef179 ef14
  have ef264 (X0 X1 X2 : G) : x ≠ ((X1 ◇ X1) ◇ x) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ y)) ◇ y) := by
    first | exact superpose ef240 ef261 | exact superpose ef261 ef240
  have ef274 (X1 : G) : x ≠ ((X1 ◇ X1) ◇ x) ◇ (y ◇ y) := by
    first | exact superpose ef15 ef264 | exact superpose ef264 ef15
  subsumption ef274 ef8

theorem Equation1049_termStructuralFrom_Equation695 :
    Law1049.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1049.models_iff]
    exact fun x y ↦ @aux695_1049 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv695_c30761ea G M h (z 0) (z 1)).symm⟩

/-- Equation 1061 `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)` holds of the term `x □ y := ((x ◇ x) ◇ x) ◇ y` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_1061 [Magma G] (h : Equation695 G) (x y z : G) :
    x = ((x ◇ x) ◇ x) ◇
      ((((((y ◇ y) ◇ y) ◇ (((z ◇ z) ◇ z) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ (((z ◇ z) ◇ z) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((z ◇ z) ◇ z) ◇ y))) ◇ z) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((x ◇ x) ◇ x) ◇
      ((((((y ◇ y) ◇ y) ◇ (((z ◇ z) ◇ z) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ (((z ◇ z) ◇ z) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((z ◇ z) ◇ z) ◇ y))) ◇ z) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef14 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef160 (X0 : G) :
      x ≠ ((x ◇ x) ◇ x) ◇ (((X0 ◇ X0) ◇ (((y ◇ y) ◇ y) ◇ (((z ◇ z) ◇ z) ◇ y))) ◇ z) := by
    first | exact superpose ef14 ef6 | exact superpose ef6 ef14
  have ef181 (X0 X1 : G) :
      x ≠ ((X0 ◇ X0) ◇ x) ◇ (((X1 ◇ X1) ◇ (((y ◇ y) ◇ y) ◇ (((z ◇ z) ◇ z) ◇ y))) ◇ z) := by
    first | exact superpose ef14 ef160 | exact superpose ef160 ef14
  have ef244 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef15 ef5 | exact superpose ef5 ef15
  have ef267 (X0 X1 X2 : G) :
      x ≠ ((X1 ◇ X1) ◇ x) ◇ (((X2 ◇ X2) ◇ (((y ◇ y) ◇ y) ◇ (((X0 ◇ X0) ◇ z) ◇ y))) ◇ z) := by
    first | exact superpose ef14 ef181 | exact superpose ef181 ef14
  have ef270 (X0 X1 X2 : G) : x ≠ ((X1 ◇ X1) ◇ x) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ z)) ◇ z) := by
    first | exact superpose ef244 ef267 | exact superpose ef267 ef244
  have ef282 (X1 : G) : x ≠ ((X1 ◇ X1) ◇ x) ◇ (z ◇ z) := by
    first | exact superpose ef15 ef270 | exact superpose ef270 ef15
  subsumption ef282 ef8

theorem Equation1061_termStructuralFrom_Equation695 :
    Law1061.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1061.models_iff]
    exact fun x y z ↦ @aux695_1061 G M h x y z
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv695_c30761ea G M h (z 0) (z 1)).symm⟩

/-- Equation 1073 `x = y ◇ ((x ◇ (x ◇ x)) ◇ y)` holds of the term `x □ y := ((x ◇ x) ◇ x) ◇ y` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_1073 [Magma G] (h : Equation695 G) (x y : G) :
    x = ((y ◇ y) ◇ y) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((y ◇ y) ◇ y) ◇
      ((((((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇
      (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef14 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef159 (X0 : G) :
      x ≠ ((y ◇ y) ◇ y) ◇ (((X0 ◇ X0) ◇ (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ y) := by
    first | exact superpose ef14 ef6 | exact superpose ef6 ef14
  have ef179 (X0 X1 : G) :
      x ≠ ((X0 ◇ X0) ◇ y) ◇ (((X1 ◇ X1) ◇ (((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ y) := by
    first | exact superpose ef14 ef159 | exact superpose ef159 ef14
  have ef240 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef15 ef5 | exact superpose ef5 ef15
  have ef261 (X0 X1 X2 : G) :
      x ≠ ((X1 ◇ X1) ◇ y) ◇ (((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ x) ◇ (((X0 ◇ X0) ◇ x) ◇ x))) ◇ y) := by
    first | exact superpose ef14 ef179 | exact superpose ef179 ef14
  have ef264 (X0 X2 : G) : x ≠ (X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ x) ◇ (((X0 ◇ X0) ◇ x) ◇ x)) := by
    first | exact superpose ef240 ef261 | exact superpose ef261 ef240
  have ef274 (X0 X2 : G) : x ≠ (X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ x) := by
    first | exact superpose ef240 ef264 | exact superpose ef264 ef240
  subsumption ef274 ef15

theorem Equation1073_termStructuralFrom_Equation695 :
    Law1073.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1073.models_iff]
    exact fun x y ↦ @aux695_1073 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv695_c30761ea G M h (z 0) (z 1)).symm⟩

/-- Equation 1075 `x = y ◇ ((x ◇ (x ◇ y)) ◇ x)` holds of the term `x □ y := ((x ◇ x) ◇ y) ◇ x` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_1075 [Magma G] (h : Equation695 G) (x y : G) :
    x = ((y ◇ y) ◇
      ((((((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x)) ◇ x) ◇
      (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x))) ◇ y := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((y ◇ y) ◇
      ((((((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x)) ◇ x) ◇
      (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x))) ◇ y := mod_symm nh
  have ef7 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X0) = X3 := superpose ef5 ef5
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ X1 = (X0 ◇ X0) ◇ (X2 ◇ X2) := superpose ef8 ef8
  have ef11 (X0 X1 X2 X3 : G) : X0 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)) = X0 ◇ (X3 ◇ X3) := by
    first | exact superpose ef5 ef8 | exact superpose ef8 ef5
  have ef14 (X0 X1 X2 : G) : (X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0)) = X2 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef16 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef22 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X1) = X3 := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef28 (X0 X1 X2 X3 X4 : G) :
      ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X3 ◇ X3) ◇ (X4 ◇ X4))) ◇ X0 = X2 := by
    first | exact superpose ef5 ef7 | exact superpose ef7 ef5
  have ef30 (X0 X1 X2 X3 X4 X5 : G) :
      X1 ◇ ((X4 ◇ X4) ◇ (X5 ◇ X5)) = ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) ◇ X0 := superpose ef7 ef7
  have ef73 (X0 X1 : G) :
      x ≠ ((y ◇ y) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ x) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x))) ◇
      y := by
    first | exact superpose ef10 ef6 | exact superpose ef6 ef10
  have ef145 (X0 : G) :
      x ≠ ((y ◇ y) ◇ (((X0 ◇ X0) ◇ x) ◇ (((x ◇ x) ◇ (((x ◇ x) ◇ y) ◇ x)) ◇ x))) ◇ y := by
    first | exact superpose ef14 ef73 | exact superpose ef73 ef14
  have ef278 (X0 X1 : G) :
      x ≠ ((y ◇ y) ◇ (((X1 ◇ X1) ◇ x) ◇ (((x ◇ x) ◇ (((X0 ◇ X0) ◇ y) ◇ x)) ◇ x))) ◇ y := by
    first | exact superpose ef15 ef145 | exact superpose ef145 ef15
  have ef323 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef16 ef5 | exact superpose ef5 ef16
  have ef365 (X0 X1 X2 : G) :
      x ≠ ((y ◇ y) ◇ (((X2 ◇ X2) ◇ x) ◇ (((x ◇ x) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y) ◇ x)) ◇ x))) ◇
      y := by
    first | exact superpose ef15 ef278 | exact superpose ef278 ef15
  have ef376 (X0 X1 : G) : x ≠ ((y ◇ y) ◇ ((x ◇ x) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y) ◇ x))) ◇ y := by
    first | exact superpose ef323 ef365 | exact superpose ef365 ef323
  have ef384 (X0 X1 : G) : x ≠ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y) ◇ x) ◇ y := by
    first | exact superpose ef16 ef376 | exact superpose ef376 ef16
  have ef1597 (X0 X1 X2 X3 X4 X5 : G) :
      (X1 ◇ ((X3 ◇ X3) ◇ X0)) ◇ ((X4 ◇ X4) ◇ (X5 ◇ X5)) = (X1 ◇ (X2 ◇ X2)) ◇ X0 := by
    first | exact superpose ef28 ef22 | exact superpose ef22 ef28
  have ef2006 (X0 X1 : G) : x ≠ ((y ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) ◇ x) ◇ y := by
    first | exact superpose ef30 ef384 | exact superpose ef384 ef30
  have ef2298 (X0 : G) : x ≠ ((y ◇ (X0 ◇ X0)) ◇ x) ◇ y := by
    first | exact superpose ef11 ef2006 | exact superpose ef2006 ef11
  have ef47888 (X0 X1 X2 : G) : x ≠ ((y ◇ ((X0 ◇ X0) ◇ x)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ y := by
    first | exact superpose ef1597 ef2298 | exact superpose ef2298 ef1597
  subsumption ef47888 ef28

theorem Equation1075_termStructuralFrom_Equation695 :
    Law1075.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) y) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law1075.models_iff]
    exact fun x y ↦ @aux695_1075 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 1) (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0))), funext fun z ↦ (@inv695_342f8883 G M h (z 0) (z 1)).symm⟩

/-- Equation 1113 `x = y ◇ ((y ◇ (x ◇ y)) ◇ y)` holds of the term `x □ y := ((x ◇ x) ◇ x) ◇ y` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_1113 [Magma G] (h : Equation695 G) (x y : G) :
    x = ((y ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      x ≠ ((y ◇ y) ◇ y) ◇
      ((((((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇
      (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef10 (X0 X1 X2 : G) : X1 ◇ X1 = (X0 ◇ X0) ◇ (X2 ◇ X2) := superpose ef8 ef8
  have ef14 (X0 X1 X2 : G) : (X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ X0)) = X2 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef16 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef68 (X0 X1 : G) :
      x ≠ ((y ◇ y) ◇ y) ◇
      ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ y) := by
    first | exact superpose ef10 ef6 | exact superpose ef6 ef10
  have ef145 (X0 : G) :
      x ≠ ((y ◇ y) ◇ y) ◇ (((X0 ◇ X0) ◇ (((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ y) := by
    first | exact superpose ef14 ef68 | exact superpose ef68 ef14
  have ef272 (X0 X1 : G) :
      x ≠ ((X0 ◇ X0) ◇ y) ◇ (((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y))) ◇ y) := by
    first | exact superpose ef15 ef145 | exact superpose ef145 ef15
  have ef319 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef16 ef5 | exact superpose ef5 ef16
  have ef361 (X0 X1 X2 : G) :
      x ≠ ((X1 ◇ X1) ◇ y) ◇ (((X2 ◇ X2) ◇ (((X1 ◇ X1) ◇ y) ◇ (((X0 ◇ X0) ◇ x) ◇ y))) ◇ y) := by
    first | exact superpose ef15 ef272 | exact superpose ef272 ef15
  have ef364 (X0 X1 X2 : G) : x ≠ (X2 ◇ X2) ◇ (((X1 ◇ X1) ◇ y) ◇ (((X0 ◇ X0) ◇ x) ◇ y)) := by
    first | exact superpose ef319 ef361 | exact superpose ef361 ef319
  have ef366 (X0 X2 : G) : x ≠ (X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ x) := by
    first | exact superpose ef319 ef364 | exact superpose ef364 ef319
  subsumption ef366 ef16

theorem Equation1113_termStructuralFrom_Equation695 :
    Law1113.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1113.models_iff]
    exact fun x y ↦ @aux695_1113 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv695_c30761ea G M h (z 0) (z 1)).symm⟩

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` holds of the term `x □ y := ((x ◇ x) ◇ x) ◇ y` over
any magma satisfying equation 695 `x = y ◇ (x ◇ ((z ◇ z) ◇ y))`. -/
private theorem aux695_4273 [Magma G] (h : Equation695 G) (x y : G) :
    ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) = ((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y) := by
  by_contra nh
  have ef5 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1)) = X0 := mod_symm (h ..)
  have ef6 :
      ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) ≠ ((y ◇ y) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y) := mod_symm nh
  have ef8 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0) = X2 := superpose ef5 ef5
  have ef14 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ X0 = (X1 ◇ X1) ◇ X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef15 (X0 X1 X2 : G) : (X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0) = X0 := by
    first | exact superpose ef8 ef5 | exact superpose ef5 ef8
  have ef160 (X0 : G) :
      ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) ≠ ((X0 ◇ X0) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y) := by
    first | exact superpose ef14 ef6 | exact superpose ef6 ef14
  have ef235 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef15 ef5 | exact superpose ef5 ef15
  have ef245 (X0 X1 : G) :
      ((x ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) ≠ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y) ◇
      (((x ◇ x) ◇ x) ◇ y) := by
    first | exact superpose ef14 ef160 | exact superpose ef160 ef14
  have ef250 (X0 X1 : G) : (x ◇ x) ◇ x ≠ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y) := by
    first | exact superpose ef235 ef245 | exact superpose ef245 ef235
  have ef340 (X0 : G) : (x ◇ x) ◇ x ≠ ((X0 ◇ X0) ◇ y) ◇ (((x ◇ x) ◇ x) ◇ y) := by
    first | exact superpose ef14 ef250 | exact superpose ef250 ef14
  subsumption ef340 ef235

theorem Equation4273_termStructuralFrom_Equation695 :
    Law4273.TermStructuralFrom Law695 := by
  intro G M hGL
  have h : Equation695 G := Law695.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) x) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law4273.models_iff]
    exact fun x y ↦ @aux695_4273 G M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0)) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), funext fun z ↦ (@inv695_c30761ea G M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := ((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ x)` of equation 713
`x = y ◇ (y ◇ ((y ◇ x) ◇ x))` can be undone: the operation is recovered as
`x ◇ y = (y ◇ y) ◇ ((x ◇ x) ◇ x)` read in `□` over a finite carrier. -/
private theorem inv713_76b261def [Finite G] [Magma G] (h : Equation713 G) (x y : G) :
    (((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ ((((y ◇ y) ◇
      (y ◇ y)) ◇ (y ◇ y)) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ y))) = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (b ◇ a))) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ (b ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ (b ◇ a)) ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ (b ◇ z)) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      (((((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ ((((y ◇ y) ◇
      (y ◇ y)) ◇ (y ◇ y)) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇ (y ◇ y))) ≠ x ◇ y := mod_symm nh
  have ef12 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef17 (X0 X1 : G) :
      X1 ◇ (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef26 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ X0 := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  have ef68 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    first | exact superpose ef26 ef7 | exact superpose ef7 ef26
  have ef70 :
      x ◇ y ≠ (((((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ (((y ◇ y) ◇ (y ◇
      y)) ◇ ((y ◇ y) ◇ (y ◇ y))) := by
    first | exact superpose ef26 ef10 | exact superpose ef10 ef26
  have ef71 :
      x ◇ y ≠ (((((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))))) ◇ (((y ◇ y) ◇ (y ◇ y)) ◇
      ((y ◇ y) ◇ (y ◇ y))) := by
    first | exact superpose ef26 ef70 | exact superpose ef70 ef26
  have ef73 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef26 ef68 | exact superpose ef68 ef26
  have ef210 (X0 : G) :
      (X0 ◇ X0) ◇ (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇
      ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef26 ef17 | exact superpose ef17 ef26
  have ef241 (X0 : G) : X0 ◇ ((X0 ◇ X0) ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef73 ef210 | exact superpose ef210 ef73
  have ef253 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef26 ef241 | exact superpose ef241 ef26
  have ef259 :
      x ◇ y ≠ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((y ◇ y) ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ (y ◇ y))) := by
    first | exact superpose ef73 ef71 | exact superpose ef71 ef73
  have ef285 :
      x ◇ y ≠ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ (y ◇ y))) := by
    first | exact superpose ef253 ef259 | exact superpose ef259 ef253
  have ef295 : x ◇ y ≠ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y := by
    first | exact superpose ef73 ef285 | exact superpose ef285 ef73
  have ef302 : x ◇ y ≠ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y := by
    first | exact superpose ef253 ef295 | exact superpose ef295 ef253
  have ef307 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef73 ef302 | exact superpose ef302 ef73
  exact absurd rfl ef307

/-- Equation 307 `x ◇ x = x ◇ (x ◇ x)` holds of the term `x □ y := ((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ x)`
over any finite magma satisfying equation 713 `x = y ◇ (y ◇ ((y ◇ x) ◇ x))`. -/
private theorem aux713_307 [Finite G] [Magma G] (h : Equation713 G) (x : G) :
    ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) =
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (b ◇ a))) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ (b ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ (b ◇ a)) ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ (b ◇ z)) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇
      x) ≠ (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x) := mod_symm nh
  have ef12 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef17 (X0 X1 : G) :
      X1 ◇ (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef26 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ X0 := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  have ef28 (X0 : G) : X0 ◇ ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0) := by
    first | exact superpose ef12 ef8 | exact superpose ef8 ef12
  have ef62 :
      (x ◇ x) ◇ (x ◇ x) ≠ ((((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x) := by
    first | exact superpose ef26 ef10 | exact superpose ef10 ef26
  have ef64 (X0 : G) : X0 ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef26 ef7 | exact superpose ef7 ef26
  have ef69 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    first | exact superpose ef26 ef7 | exact superpose ef7 ef26
  have ef70 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef26 ef69 | exact superpose ef69 ef26
  have ef204 (X0 : G) :
      X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := by
    first | exact superpose ef64 ef17 | exact superpose ef17 ef64
  have ef207 (X0 : G) :
      (X0 ◇ X0) ◇ (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇
      ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef26 ef17 | exact superpose ef17 ef26
  have ef238 (X0 : G) : X0 ◇ ((X0 ◇ X0) ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef70 ef207 | exact superpose ef207 ef70
  have ef240 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    first | exact superpose ef26 ef204 | exact superpose ef204 ef26
  have ef250 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef26 ef238 | exact superpose ef238 ef26
  have ef439 (X0 : G) :
      (X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇
      ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇
      ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇
      ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    first | exact superpose ef28 ef17 | exact superpose ef17 ef28
  have ef442 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) =
      ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇
      ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef26 ef439 | exact superpose ef439 ef26
  have ef453 (X0 : G) :
      (X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef240 ef442 | exact superpose ef442 ef240
  have ef460 (X0 : G) :
      (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef26 ef453 | exact superpose ef453 ef26
  have ef462 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef70 ef460 | exact superpose ef460 ef70
  have ef592 :
      (x ◇ x) ◇ (x ◇ x) ≠ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      (x ◇ x) := by
    first | exact superpose ef250 ef62 | exact superpose ef62 ef250
  have ef627 : (x ◇ x) ◇ (x ◇ x) ≠ (x ◇ x) ◇ (x ◇ x) := by
    first | exact superpose ef462 ef592 | exact superpose ef592 ef462
  exact absurd rfl ef627

theorem Equation307_termStructuralFromFin_Equation713 :
    Law307.TermStructuralFromFin Law713 := by
  intro G _ M hGL
  have h : Equation713 G := Law713.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) (M.op y y)) (M.op x x))⟩, ?_, ?_, ?_⟩
  · rw [@Law307.models_iff]
    exact fun x ↦ @aux713_307 G _ M h x
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (tm (Term.var 1) (Term.var 1))) (tm (Term.var 0) (Term.var 0))), rfl⟩
  · exact ⟨(tm (tm (Term.var 1) (Term.var 1)) (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0))), funext fun z ↦ (@inv713_76b261def G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := ((x ◇ x) ◇ (x ◇ x)) ◇ y` of equation 713
`x = y ◇ (y ◇ ((y ◇ x) ◇ x))` can be undone: the operation is recovered as `x ◇ y = (x ◇ x) ◇ y`
read in `□` over a finite carrier. -/
private theorem inv713_979d3bc2f [Finite G] [Magma G] (h : Equation713 G) (x y : G) :
    (((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ y = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (b ◇ a))) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ (b ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ (b ◇ a)) ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ (b ◇ z)) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      (((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ y ≠ x ◇ y := mod_symm nh
  have ef12 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef17 (X0 X1 : G) :
      X1 ◇ (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef26 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ X0 := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  have ef68 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    first | exact superpose ef26 ef7 | exact superpose ef7 ef26
  have ef69 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef26 ef68 | exact superpose ef68 ef26
  have ef235 (X0 : G) :
      (X0 ◇ X0) ◇ (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇
      ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef26 ef17 | exact superpose ef17 ef26
  have ef268 (X0 : G) : X0 ◇ ((X0 ◇ X0) ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef69 ef235 | exact superpose ef235 ef69
  have ef282 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef26 ef268 | exact superpose ef268 ef26
  have ef397 :
      x ◇
      y ≠ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇
      y := by
    first | exact superpose ef282 ef10 | exact superpose ef10 ef282
  have ef399 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef282 ef69 | exact superpose ef69 ef282
  have ef422 : x ◇ y ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ y := by
    first | exact superpose ef282 ef397 | exact superpose ef397 ef282
  have ef566 (X0 : G) : X0 ◇ X0 = ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef69 ef399 | exact superpose ef399 ef69
  have ef587 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef282 ef566 | exact superpose ef566 ef282
  have ef741 : x ◇ y ≠ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ y := by
    first | exact superpose ef587 ef422 | exact superpose ef422 ef587
  have ef764 : x ◇ y ≠ x ◇ y := by
    first | exact superpose ef69 ef741 | exact superpose ef741 ef69
  exact absurd rfl ef764

/-- Equation 817 `x = x ◇ ((x ◇ x) ◇ (x ◇ x))` holds of the term `x □ y := ((x ◇ x) ◇ (x ◇ x)) ◇ y`
over any finite magma satisfying equation 713 `x = y ◇ (y ◇ ((y ◇ x) ◇ x))`. -/
private theorem aux713_817 [Finite G] [Magma G] (h : Equation713 G) (x : G) :
    x = ((x ◇ x) ◇ (x ◇ x)) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (b ◇ a))) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ (b ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ (b ◇ a)) ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ (b ◇ z)) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      x ≠ ((x ◇ x) ◇ (x ◇ x)) ◇ ((((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      x)) := mod_symm nh
  have ef12 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef17 (X0 X1 : G) :
      X1 ◇ (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef26 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ X0 := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  have ef68 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    first | exact superpose ef26 ef7 | exact superpose ef7 ef26
  have ef69 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef26 ef68 | exact superpose ef68 ef26
  have ef235 (X0 : G) :
      (X0 ◇ X0) ◇ (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇
      ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef26 ef17 | exact superpose ef17 ef26
  have ef268 (X0 : G) : X0 ◇ ((X0 ◇ X0) ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef69 ef235 | exact superpose ef235 ef69
  have ef282 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef26 ef268 | exact superpose ef268 ef26
  have ef395 (X0 : G) :
      (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = (X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)) := superpose ef282 ef282
  have ef397 :
      x ≠ (x ◇ (x ◇ x)) ◇
      (((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef282 ef10 | exact superpose ef10 ef282
  have ef399 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef282 ef69 | exact superpose ef69 ef282
  have ef422 :
      x ≠ (x ◇ (x ◇ x)) ◇ ((((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef282 ef397 | exact superpose ef397 ef282
  have ef424 (X0 : G) : (X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef399 ef395 | exact superpose ef395 ef399
  have ef566 (X0 : G) : X0 ◇ X0 = ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef69 ef399 | exact superpose ef399 ef69
  have ef587 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef282 ef566 | exact superpose ef566 ef282
  have ef742 : x ≠ (x ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ x)) := by
    first | exact superpose ef587 ef422 | exact superpose ef422 ef587
  have ef765 : x ≠ (x ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)) := by
    first | exact superpose ef587 ef742 | exact superpose ef742 ef587
  have ef779 : x ≠ (x ◇ (x ◇ x)) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef282 ef765 | exact superpose ef765 ef282
  subsumption ef779 ef424

theorem Equation817_termStructuralFromFin_Equation713 :
    Law817.TermStructuralFromFin Law713 := by
  intro G _ M hGL
  have h : Equation713 G := Law713.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) (M.op x x)) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law817.models_iff]
    exact fun x ↦ @aux713_817 G _ M h x
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), funext fun z ↦ (@inv713_979d3bc2f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 1426 `x = (x ◇ x) ◇ (x ◇ (x ◇ x))` holds of the term `x □ y := ((x ◇ x) ◇ (x ◇ x)) ◇ y`
over any finite magma satisfying equation 713 `x = y ◇ (y ◇ ((y ◇ x) ◇ x))`. -/
private theorem aux713_1426 [Finite G] [Magma G] (h : Equation713 G) (x : G) :
    x = (((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (b ◇ a))) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ (b ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ (b ◇ a)) ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ (b ◇ z)) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      x ≠ (((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ x))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ x)) := mod_symm nh
  have ef12 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef13 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0) := superpose ef9 ef9
  have ef17 (X0 X1 : G) :
      X1 ◇ (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef26 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ X0 := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  have ef63 (X0 : G) : X0 ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef26 ef7 | exact superpose ef7 ef26
  have ef68 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    first | exact superpose ef26 ef7 | exact superpose ef7 ef26
  have ef69 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef26 ef68 | exact superpose ef68 ef26
  have ef235 (X0 : G) :
      (X0 ◇ X0) ◇ (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇
      ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef26 ef17 | exact superpose ef17 ef26
  have ef268 (X0 : G) : X0 ◇ ((X0 ◇ X0) ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef69 ef235 | exact superpose ef235 ef69
  have ef282 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef26 ef268 | exact superpose ef268 ef26
  have ef397 :
      x ≠ ((((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇
      (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef282 ef10 | exact superpose ef10 ef282
  have ef399 (X0 : G) : (X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef282 ef69 | exact superpose ef69 ef282
  have ef422 :
      x ≠ (((x ◇ (x ◇ x)) ◇ x) ◇ (((x ◇ (x ◇ x)) ◇ x) ◇ ((x ◇ (x ◇ x)) ◇ x))) ◇
      ((x ◇ (x ◇ x)) ◇ ((x ◇ (x ◇ x)) ◇ x)) := by
    first | exact superpose ef282 ef397 | exact superpose ef397 ef282
  have ef566 (X0 : G) : X0 ◇ X0 = ((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef69 ef399 | exact superpose ef399 ef69
  have ef587 (X0 : G) : X0 ◇ X0 = (X0 ◇ (X0 ◇ X0)) ◇ X0 := by
    first | exact superpose ef282 ef566 | exact superpose ef566 ef282
  have ef741 : x ≠ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x)) := by
    first | exact superpose ef587 ef422 | exact superpose ef422 ef587
  have ef764 : x ≠ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ ((x ◇ x) ◇ x)) := by
    first | exact superpose ef13 ef741 | exact superpose ef741 ef13
  have ef777 : x ≠ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef26 ef764 | exact superpose ef764 ef26
  have ef787 : x ≠ x ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef69 ef777 | exact superpose ef777 ef69
  subsumption ef787 ef63

theorem Equation1426_termStructuralFromFin_Equation713 :
    Law1426.TermStructuralFromFin Law713 := by
  intro G _ M hGL
  have h : Equation713 G := Law713.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x x) (M.op x x)) y)⟩, ?_, ?_, ?_⟩
  · rw [@Law1426.models_iff]
    exact fun x ↦ @aux713_1426 G _ M h x
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 0)) (tm (Term.var 0) (Term.var 0))) (Term.var 1)), rfl⟩
  · exact ⟨(tm (tm (Term.var 0) (Term.var 0)) (Term.var 1)), funext fun z ↦ (@inv713_979d3bc2f G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3253 `x ◇ x = x ◇ (x ◇ (x ◇ x))` holds of the term
`x □ y := ((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ x)` over any finite magma satisfying equation 713
`x = y ◇ (y ◇ ((y ◇ x) ◇ x))`. -/
private theorem aux713_3253 [Finite G] [Magma G] (h : Equation713 G) (x : G) :
    ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) =
      ((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x))) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (x ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (b ◇ a))) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ (b ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ (b ◇ a)) ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ (b ◇ z)) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇
      x) ≠ ((((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x))) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (x ◇
      x) := mod_symm nh
  have ef12 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef17 (X0 X1 : G) :
      X1 ◇ (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef26 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ X0 := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  have ef68 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    first | exact superpose ef26 ef7 | exact superpose ef7 ef26
  have ef70 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef26 ef68 | exact superpose ef68 ef26
  have ef236 (X0 : G) :
      (X0 ◇ X0) ◇ (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇
      ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef26 ef17 | exact superpose ef17 ef26
  have ef269 (X0 : G) : X0 ◇ ((X0 ◇ X0) ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef70 ef236 | exact superpose ef236 ef70
  have ef283 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef26 ef269 | exact superpose ef269 ef26
  have ef398 :
      ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) ≠ (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      (((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (x ◇
      x) := by
    first | exact superpose ef283 ef10 | exact superpose ef10 ef283
  have ef423 :
      ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) ≠ ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      (((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (x ◇
      x) := by
    first | exact superpose ef283 ef398 | exact superpose ef398 ef283
  have ef432 :
      (x ◇ x) ◇ (x ◇ x) ≠ (((((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      (x ◇ x)) ◇ (((((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇ (x ◇ x)))) ◇ (x ◇
      x) := by
    first | exact superpose ef26 ef423 | exact superpose ef423 ef26
  have ef438 :
      (x ◇ x) ◇ (x ◇ x) ≠ (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      (x ◇ x) := by
    first | exact superpose ef70 ef432 | exact superpose ef432 ef70
  have ef442 : (x ◇ x) ◇ (x ◇ x) ≠ (x ◇ x) ◇ (x ◇ x) := by
    first | exact superpose ef70 ef438 | exact superpose ef438 ef70
  exact absurd rfl ef442

theorem Equation3253_termStructuralFromFin_Equation713 :
    Law3253.TermStructuralFromFin Law713 := by
  intro G _ M hGL
  have h : Equation713 G := Law713.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) (M.op y y)) (M.op x x))⟩, ?_, ?_, ?_⟩
  · rw [@Law3253.models_iff]
    exact fun x ↦ @aux713_3253 G _ M h x
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (tm (Term.var 1) (Term.var 1))) (tm (Term.var 0) (Term.var 0))), rfl⟩
  · exact ⟨(tm (tm (Term.var 1) (Term.var 1)) (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0))), funext fun z ↦ (@inv713_76b261def G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3456 `x ◇ x = x ◇ ((x ◇ x) ◇ x)` holds of the term
`x □ y := ((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ x)` over any finite magma satisfying equation 713
`x = y ◇ (y ◇ ((y ◇ x) ◇ x))`. -/
private theorem aux713_3456 [Finite G] [Magma G] (h : Equation713 G) (x : G) :
    ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) = (((((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ (x ◇ x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (b ◇ a))) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ (b ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : b ◇ ((b ◇ (b ◇ a)) ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ (b ◇ z)) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b) a
  have ef7 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot1 ..)
  have ef10 :
      ((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x) ≠ (((((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x))))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ (x ◇ x)))))) ◇ (x ◇
      x) := mod_symm nh
  have ef12 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))) := by
    first | exact superpose ef7 ef9 | exact superpose ef9 ef7
  have ef17 (X0 X1 : G) :
      X1 ◇ (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef26 (X0 : G) : X0 ◇ X0 = (X0 ◇ X0) ◇ X0 := by
    first | exact superpose ef7 ef12 | exact superpose ef12 ef7
  have ef68 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    first | exact superpose ef26 ef7 | exact superpose ef7 ef26
  have ef69 :
      (x ◇ x) ◇ (x ◇ x) ≠ (((((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))))) ◇
      ((((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))) ◇
      (((x ◇ x) ◇ (x ◇ x)) ◇ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x)))))) ◇ (x ◇ x) := by
    first | exact superpose ef26 ef10 | exact superpose ef10 ef26
  have ef70 (X0 : G) : (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    first | exact superpose ef26 ef68 | exact superpose ef68 ef26
  have ef207 (X0 : G) :
      (X0 ◇ X0) ◇ (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇
      ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ X0) := by
    first | exact superpose ef26 ef17 | exact superpose ef17 ef26
  have ef238 (X0 : G) : X0 ◇ ((X0 ◇ X0) ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef70 ef207 | exact superpose ef207 ef70
  have ef250 (X0 : G) : X0 ◇ (X0 ◇ X0) = (X0 ◇ X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef26 ef238 | exact superpose ef238 ef26
  have ef256 : (x ◇ x) ◇ (x ◇ x) ≠ (((x ◇ x) ◇ (x ◇ x)) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ x) := by
    first | exact superpose ef70 ef69 | exact superpose ef69 ef70
  have ef282 : (x ◇ x) ◇ (x ◇ x) ≠ ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))) ◇ (x ◇ x) := by
    first | exact superpose ef250 ef256 | exact superpose ef256 ef250
  have ef292 : (x ◇ x) ◇ (x ◇ x) ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef70 ef282 | exact superpose ef282 ef70
  subsumption ef292 ef250

theorem Equation3456_termStructuralFromFin_Equation713 :
    Law3456.TermStructuralFromFin Law713 := by
  intro G _ M hGL
  have h : Equation713 G := Law713.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op y y) (M.op y y)) (M.op x x))⟩, ?_, ?_, ?_⟩
  · rw [@Law3456.models_iff]
    exact fun x ↦ @aux713_3456 G _ M h x
  · exact ⟨(tm (tm (tm (Term.var 1) (Term.var 1)) (tm (Term.var 1) (Term.var 1))) (tm (Term.var 0) (Term.var 0))), rfl⟩
  · exact ⟨(tm (tm (Term.var 1) (Term.var 1)) (tm (tm (Term.var 0) (Term.var 0)) (Term.var 0))), funext fun z ↦ (@inv713_76b261def G _ M h (z 0) (z 1)).symm⟩

/-- The defining term `x □ y := ((x ◇ y) ◇ x) ◇ x` of equation 1289 `x = y ◇ (((x ◇ y) ◇ y) ◇ y)`
can be undone: the operation is recovered as `x ◇ y = x ◇ (x ◇ (x ◇ y))` read in `□` over a
finite carrier. -/
private theorem inv1289_d04c27faf [Finite G] [Magma G] (h : Equation1289 G) (x y : G) :
    ((x ◇ (((x ◇ (((x ◇ y) ◇ x) ◇ x)) ◇ x) ◇ x)) ◇ x) ◇ x = x ◇ y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ ((a ◇ b) ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((z ◇ b) ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have ef9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef12 : x ◇ y ≠ ((x ◇ (((x ◇ (((x ◇ y) ◇ x) ◇ x)) ◇ x) ◇ x)) ◇ x) ◇ x := mod_symm nh
  have ef17 : x ◇ y ≠ (x ◇ (((x ◇ y) ◇ x) ◇ x)) ◇ x := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  subsumption ef17 ef9

/-- Equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` holds of the term `x □ y := ((x ◇ y) ◇ x) ◇ x` over
any finite magma satisfying equation 1289 `x = y ◇ (((x ◇ y) ◇ y) ◇ y)`. -/
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

theorem Equation464_termStructuralFromFin_Equation1289 :
    Law464.TermStructuralFromFin Law1289 := by
  intro G _ M hGL
  have h : Equation1289 G := Law1289.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) x) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law464.models_iff]
    exact fun x y ↦ @aux1289_464 G _ M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv1289_d04c27faf G _ M h (z 0) (z 1)).symm⟩

/-- Equation 1629 `x = (x ◇ x) ◇ ((x ◇ x) ◇ x)` holds of the term `x □ y := ((x ◇ y) ◇ x) ◇ x` over
any finite magma satisfying equation 1289 `x = y ◇ (((x ◇ y) ◇ y) ◇ y)`. -/
private theorem aux1289_1629 [Finite G] [Magma G] (h : Equation1289 G) (x : G) :
    x = (((((x ◇ x) ◇ x) ◇ x) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ x) ◇
      x)) ◇ (((x ◇ x) ◇ x) ◇ x) := by
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
  have ef8 (X0 X1 : G) : X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef11 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1 = X0 := mod_symm (hrot2 ..)
  have ef12 :
      x ≠ (((((x ◇ x) ◇ x) ◇ x) ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ x) ◇
      x)) ◇ (((x ◇ x) ◇ x) ◇ x) := mod_symm nh
  have ef16 : x ≠ ((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x) := by
    first | exact superpose ef9 ef12 | exact superpose ef12 ef9
  have ef17 : x ≠ x ◇ (((x ◇ x) ◇ x) ◇ x) := by
    first | exact superpose ef11 ef16 | exact superpose ef16 ef11
  subsumption ef17 ef8

theorem Equation1629_termStructuralFromFin_Equation1289 :
    Law1629.TermStructuralFromFin Law1289 := by
  intro G _ M hGL
  have h : Equation1289 G := Law1289.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) x) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law1629.models_iff]
    exact fun x ↦ @aux1289_1629 G _ M h x
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv1289_d04c27faf G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3456 `x ◇ x = x ◇ ((x ◇ x) ◇ x)` holds of the term `x □ y := ((x ◇ y) ◇ x) ◇ x` over
any finite magma satisfying equation 1289 `x = y ◇ (((x ◇ y) ◇ y) ◇ y)`. -/
private theorem aux1289_3456 [Finite G] [Magma G] (h : Equation1289 G) (x : G) :
    ((x ◇ x) ◇ x) ◇ x =
      ((x ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ x) ◇ x := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ ((a ◇ b) ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((z ◇ b) ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ (a ◇ b)) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (z ◇ b)) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef8 (X0 X1 : G) : X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef12 :
      ((x ◇ x) ◇ x) ◇
      x ≠ ((x ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ x) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ x) ◇
      x := mod_symm nh
  have ef13 (X0 X1 : G) :
      (((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) =
      X1 := superpose ef8 ef8
  have ef15 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X0 ◇ X1)) ◇ X1 := superpose ef9 ef9
  have ef20 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := by
    first | exact superpose ef10 ef9 | exact superpose ef9 ef10
  have ef53 :
      ((x ◇ x) ◇ x) ◇
      x ≠ ((x ◇ (((((x ◇ x) ◇ x) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ x) ◇
      x := by
    first | exact superpose ef20 ef12 | exact superpose ef12 ef20
  have ef62 :
      ((x ◇ x) ◇ x) ◇
      x ≠ (x ◇ ((((((x ◇ x) ◇ x) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ x)) ◇
      x := by
    first | exact superpose ef20 ef53 | exact superpose ef53 ef20
  have ef70 :
      ((x ◇ x) ◇ x) ◇ x ≠ x ◇
      (((((((x ◇ x) ◇ x) ◇ x) ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ x) ◇ x) := by
    first | exact superpose ef15 ef62 | exact superpose ef62 ef15
  have ef76 :
      ((x ◇ x) ◇ x) ◇ x ≠ x ◇
      ((((((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ (((x ◇ x) ◇ x) ◇ x)) ◇ (((x ◇ x) ◇ x) ◇ x))) ◇ x) ◇ x) := by
    first | exact superpose ef15 ef70 | exact superpose ef70 ef15
  have ef80 : ((x ◇ x) ◇ x) ◇ x ≠ x ◇ ((x ◇ x) ◇ x) := by
    first | exact superpose ef13 ef76 | exact superpose ef76 ef13
  have ef83 : (x ◇ (x ◇ x)) ◇ x ≠ x ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef20 ef80 | exact superpose ef80 ef20
  have ef86 : x ◇ ((x ◇ x) ◇ x) ≠ x ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef15 ef83 | exact superpose ef83 ef15
  have ef89 : x ◇ (x ◇ (x ◇ x)) ≠ x ◇ (x ◇ (x ◇ x)) := by
    first | exact superpose ef20 ef86 | exact superpose ef86 ef20
  exact absurd rfl ef89

theorem Equation3456_termStructuralFromFin_Equation1289 :
    Law3456.TermStructuralFromFin Law1289 := by
  intro G _ M hGL
  have h : Equation1289 G := Law1289.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) x) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law3456.models_iff]
    exact fun x ↦ @aux1289_3456 G _ M h x
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv1289_d04c27faf G _ M h (z 0) (z 1)).symm⟩

/-- Equation 3522 `x ◇ y = x ◇ ((y ◇ y) ◇ y)` holds of the term `x □ y := ((x ◇ y) ◇ x) ◇ x` over
any finite magma satisfying equation 1289 `x = y ◇ (((x ◇ y) ◇ y) ◇ y)`. -/
private theorem aux1289_3522 [Finite G] [Magma G] (h : Equation1289 G) (x y : G) :
    ((x ◇ y) ◇ x) ◇ x =
      ((x ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ x) ◇ x := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ ((a ◇ b) ◇ b)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((z ◇ b) ◇ b)) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ (a ◇ b)) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (z ◇ b)) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef8 (X0 X1 : G) : X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef9 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1 = X0 := mod_symm (hrot0 ..)
  have ef10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef12 :
      ((x ◇ y) ◇ x) ◇
      x ≠ ((x ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ x) ◇
      x := mod_symm nh
  have ef13 (X0 X1 : G) :
      (((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) =
      X1 := superpose ef8 ef8
  have ef15 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X0 ◇ X1)) ◇ X1 := superpose ef9 ef9
  have ef20 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = (X1 ◇ X0) ◇ X1 := by
    first | exact superpose ef10 ef9 | exact superpose ef9 ef10
  have ef55 :
      ((x ◇ y) ◇ x) ◇
      x ≠ ((x ◇ (((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ x) ◇
      x := by
    first | exact superpose ef20 ef12 | exact superpose ef12 ef20
  have ef64 :
      ((x ◇ y) ◇ x) ◇
      x ≠ (x ◇ ((((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x)) ◇
      x := by
    first | exact superpose ef20 ef55 | exact superpose ef55 ef20
  have ef72 :
      ((x ◇ y) ◇ x) ◇ x ≠ x ◇
      (((((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ x) ◇ x) := by
    first | exact superpose ef15 ef64 | exact superpose ef64 ef15
  have ef78 :
      ((x ◇ y) ◇ x) ◇ x ≠ x ◇
      ((((((y ◇ y) ◇ y) ◇ y) ◇ ((y ◇ (((y ◇ y) ◇ y) ◇ y)) ◇ (((y ◇ y) ◇ y) ◇ y))) ◇ x) ◇ x) := by
    first | exact superpose ef15 ef72 | exact superpose ef72 ef15
  have ef82 : ((x ◇ y) ◇ x) ◇ x ≠ x ◇ ((y ◇ x) ◇ x) := by
    first | exact superpose ef13 ef78 | exact superpose ef78 ef13
  have ef85 : (x ◇ (y ◇ x)) ◇ x ≠ x ◇ ((y ◇ x) ◇ x) := by
    first | exact superpose ef20 ef82 | exact superpose ef82 ef20
  subsumption ef85 ef15

theorem Equation3522_termStructuralFromFin_Equation1289 :
    Law3522.TermStructuralFromFin Law1289 := by
  intro G _ M hGL
  have h : Equation1289 G := Law1289.models_iff.mp hGL
  refine ⟨⟨fun x y ↦ (M.op (M.op (M.op x y) x) x)⟩, ?_, ?_, ?_⟩
  · rw [@Law3522.models_iff]
    exact fun x y ↦ @aux1289_3522 G _ M h x y
  · exact ⟨(tm (tm (tm (Term.var 0) (Term.var 1)) (Term.var 0)) (Term.var 0)), rfl⟩
  · exact ⟨(tm (Term.var 0) (tm (Term.var 0) (tm (Term.var 0) (Term.var 1)))), funext fun z ↦ (@inv1289_d04c27faf G _ M h (z 0) (z 1)).symm⟩

end Law.MagmaLaw
