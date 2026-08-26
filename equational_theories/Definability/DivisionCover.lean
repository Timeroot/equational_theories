import equational_theories.Definability.DivisionStructural
import equational_theories.Equations.All
import equational_theories.Superposition
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
-- a cell rarely needs all four division axioms, and which ones it needs is Vampire's business
set_option linter.unusedVariables false

/-!
# Term-structural facts whose witness is a model-dependent division

The sources below force every translation of a finite model to be injective, hence -- finiteness
again -- bijective. The left division `x \ y` is then the inverse translation `L_x⁻¹ y`, which is
`L_x^N y` for an exponent `N` read off the carrier: a magma term whose *shape* depends on the model.
`TermStructuralFromFin` quantifies the magma before the term, so this is a legal witness, and it is
one that `paras.py`'s uniform search cannot see. Over all magmas nothing is gained this way -- a
provable `∀ x y ∃ z, x ◇ z = y` is an equational consequence, and equational logic has no case
splits, so the existential always has a single term witness. What is genuinely finite here is that
the hypothesis being spent, injectivity, is a Horn clause rather than an equation.

`Definability/DivisionStructural.lean` carries the argument, including the inverse direction that
makes these *structural* rather than merely definable: if `L_x^(N+1) = id` then `N` iterations of
`L_x^N` are `L_x` again, so the operation is a term in the division exactly as the division is a
term in the operation.

Each cell contributes three replayed lemmas: `inj<s>R` and `inj<s>L`, the injectivity of the two
translations, and `aux<s>_<t><side>`, which says the target law holds of that division in any
structure carrying two-sided divisions.
-/

open FirstOrder.Language
open Law
open Law.MagmaLaw

namespace Law.MagmaLaw

variable {G : Type}

/-- On a finite carrier a one-sided inverse is two-sided: this is what turns a source law into its
cyclic rotations. Applied with `f` the outer part of the chain and `g` its first factor, it moves
`g` from the inside of the composite to the outside. -/
private theorem rot_of_finite [Finite G] {f g : G → G} (hfg : ∀ z, f (g z) = z) (x : G) :
    g (f x) = x := by
  have hs : Function.Surjective f := fun z ↦ ⟨g z, hfg z⟩
  exact Finite.injective_iff_surjective.mpr hs (hfg (f x))

/-- Right translation by `t` is injective in every finite magma satisfying equation 66
`x = y ◇ (x ◇ (y ◇ y))`. Its models are therefore quasigroups, and the division is the inverse
translation -- a term, at an exponent the carrier fixes. -/
private theorem inj66R [Finite G] [Magma G] (h : Equation66 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef9 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef12 : t = (p ◇ t) ◇ (q ◇ q) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef13 (X0 X1 : G) : X1 ◇ X1 = X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef8 ef8
  have ef17 : q ◇ q = t ◇ ((p ◇ t) ◇ (p ◇ t)) := by
    first | exact superpose ef12 ef8 | exact superpose ef8 ef12
  have ef18 : q ◇ q = p ◇ p := by
    first | exact superpose ef13 ef17 | exact superpose ef17 ef13
  have ef29 : q = (p ◇ p) ◇ (p ◇ p) := by
    first | exact superpose ef18 ef8 | exact superpose ef8 ef18
  have ef30 : p = q := by
    first | exact superpose ef8 ef29 | exact superpose ef29 ef8
  subsumption ef30 ef10

/-- Left translation by `t` is injective in every finite magma satisfying equation 66
`x = y ◇ (x ◇ (y ◇ y))`. Its models are therefore quasigroups, and the division is the inverse
translation -- a term, at an exponent the carrier fixes. -/
private theorem inj66L [Finite G] [Magma G] (h : Equation66 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef12 : q = (t ◇ p) ◇ (t ◇ t) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef16 : p = q := by
    first | exact superpose ef8 ef12 | exact superpose ef12 ef8
  subsumption ef16 ef10

/-- Equation 53 `x = x ◇ (y ◇ (x ◇ y))` holds of the left division of any magma satisfying equation
66 `x = y ◇ (x ◇ (y ◇ y))` and equipped with two-sided divisions. -/
private theorem aux66_53L [Finite G] [Magma G] (h : Equation66 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl y (dl x y)) := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl y (dl x y)) := mod_symm nh
  have ef21 (X0 X1 : G) : X0 ◇ (X1 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef54 (X0 X1 : G) : X0 ◇ X0 = dl X1 (dl X0 X1) := by
    first | exact superpose ef21 ef15 | exact superpose ef15 ef21
  have ef288 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef54 ef16 | exact superpose ef16 ef54
  subsumption ef288 ef15

theorem Equation53_termStructuralFromFin_Equation66_finiteDivision :
    Law53.TermStructuralFromFin Law66 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj66R G _ M (Law66.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj66L G _ M (Law66.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law53.models_iff]
    exact fun x y ↦
      @aux66_53L G _ M (Law66.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 2494 `x = (y ◇ ((x ◇ x) ◇ x)) ◇ y` holds of the right division of any magma satisfying
equation 66 `x = y ◇ (x ◇ (y ◇ y))` and equipped with two-sided divisions. -/
private theorem aux66_2494R [Finite G] [Magma G] (h : Equation66 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dr (dr y (dr (dr x x) x)) y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 : x ≠ dr (dr y (dr (dr x x) x)) y := mod_symm nh
  have ef19 (X0 X1 : G) : X1 ◇ X0 = dr X0 (X1 ◇ X1) := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef36 (X0 X1 : G) : (X0 ◇ X0) ◇ X1 = dr X1 X0 := by
    first | exact superpose ef11 ef19 | exact superpose ef19 ef11
  have ef204 (X0 X1 : G) : X1 ◇ X1 = dr (dr X0 X1) X0 := by
    first | exact superpose ef36 ef13 | exact superpose ef13 ef36
  have ef579 : x ≠ dr (dr y (x ◇ x)) y := by
    first | exact superpose ef204 ef16 | exact superpose ef16 ef204
  have ef580 : x ≠ (x ◇ x) ◇ (x ◇ x) := by
    first | exact superpose ef204 ef579 | exact superpose ef579 ef204
  subsumption ef580 ef11

theorem Equation2494_termStructuralFromFin_Equation66_finiteDivision :
    Law2494.TermStructuralFromFin Law66 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj66R G _ M (Law66.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj66L G _ M (Law66.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law2494.models_iff]
    exact fun x y ↦
      @aux66_2494R G _ M (Law66.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 115
`x = y ◇ ((x ◇ x) ◇ y)`. Its models are therefore quasigroups, and the division is the inverse
translation -- a term, at an exponent the carrier fixes. -/
private theorem inj115R [Finite G] [Magma G] (h : Equation115 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef9 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef11 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef19 : q = (t ◇ (p ◇ t)) ◇ (t ◇ (p ◇ t)) := by
    first | exact superpose ef11 ef9 | exact superpose ef9 ef11
  have ef27 : p = q := by
    first | exact superpose ef9 ef19 | exact superpose ef19 ef9
  subsumption ef27 ef12

/-- Left translation by `t` is injective in every finite magma satisfying equation 115
`x = y ◇ ((x ◇ x) ◇ y)`. Its models are therefore quasigroups, and the division is the inverse
translation -- a term, at an exponent the carrier fixes. -/
private theorem inj115L [Finite G] [Magma G] (h : Equation115 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef14 : q = ((t ◇ p) ◇ (t ◇ p)) ◇ t := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef16 : p = q := by
    first | exact superpose ef10 ef14 | exact superpose ef14 ef10
  subsumption ef16 ef12

/-- Equation 221 `x = (y ◇ (x ◇ y)) ◇ x` holds of the right division of any magma satisfying
equation 115 `x = y ◇ ((x ◇ x) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux115_221R [Finite G] [Magma G] (h : Equation115 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dr (dr y (dr x y)) x := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef13 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : x ≠ dr (dr y (dr x y)) x := mod_symm nh
  have ef32 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ X0) = dr X0 X1 := by
    first | exact superpose ef13 ef15 | exact superpose ef15 ef13
  have ef105 (X0 X1 : G) : X0 ◇ X0 = dr X1 (dr X0 X1) := by
    first | exact superpose ef14 ef32 | exact superpose ef32 ef14
  have ef303 : x ≠ dr (x ◇ x) x := by
    first | exact superpose ef105 ef18 | exact superpose ef18 ef105
  subsumption ef303 ef15

theorem Equation221_termStructuralFromFin_Equation115_finiteDivision :
    Law221.TermStructuralFromFin Law115 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj115R G _ M (Law115.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj115L G _ M (Law115.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law221.models_iff]
    exact fun x y ↦
      @aux115_221R G _ M (Law115.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` holds of the right division of any magma satisfying
equation 115 `x = y ◇ ((x ◇ x) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux115_4273R [Finite G] [Magma G] (h : Equation115 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x (dr x x) = dr y (dr x y) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef11 (X0 X1 : G) : X1 ◇ ((X0 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x (dr x x) ≠ dr y (dr x y) := mod_symm nh
  have ef24 (X0 X1 : G) : dr X0 ((X0 ◇ X0) ◇ X1) = X1 := by
    first | exact superpose ef11 ef15 | exact superpose ef15 ef11
  have ef32 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ X0) = dr X0 X1 := by
    first | exact superpose ef13 ef15 | exact superpose ef15 ef13
  have ef105 (X0 X1 : G) : X0 ◇ X0 = dr X1 (dr X0 X1) := by
    first | exact superpose ef14 ef32 | exact superpose ef32 ef14
  have ef115 (X0 : G) : X0 ◇ X0 = dr X0 (dr X0 X0) := by
    first | exact superpose ef32 ef24 | exact superpose ef24 ef32
  have ef303 : dr x (dr x x) ≠ x ◇ x := by
    first | exact superpose ef105 ef18 | exact superpose ef18 ef105
  subsumption ef303 ef115

theorem Equation4273_termStructuralFromFin_Equation115_finiteDivision :
    Law4273.TermStructuralFromFin Law115 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj115R G _ M (Law115.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj115L G _ M (Law115.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4273.models_iff]
    exact fun x y ↦
      @aux115_4273R G _ M (Law115.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 125
`x = y ◇ ((y ◇ x) ◇ y)`. Its models are therefore quasigroups, and the division is the inverse
translation -- a term, at an exponent the carrier fixes. -/
private theorem inj125R [Finite G] [Magma G] (h : Equation125 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : b ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef9 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef11 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef15 : q = t ◇ (t ◇ (p ◇ t)) := by
    first | exact superpose ef11 ef9 | exact superpose ef9 ef11
  have ef19 : p = q := by
    first | exact superpose ef9 ef15 | exact superpose ef15 ef9
  subsumption ef19 ef12

/-- Left translation by `t` is injective in every finite magma satisfying equation 125
`x = y ◇ ((y ◇ x) ◇ y)`. Its models are therefore quasigroups, and the division is the inverse
translation -- a term, at an exponent the carrier fixes. -/
private theorem inj125L [Finite G] [Magma G] (h : Equation125 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have ef8 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef13 : q = t ◇ ((t ◇ p) ◇ t) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef15 : p = q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef15 ef12

/-- Equation 63 `x = y ◇ (x ◇ (x ◇ y))` holds of the left division of any magma satisfying equation
125 `x = y ◇ ((y ◇ x) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux125_63L [Finite G] [Magma G] (h : Equation125 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl y (dl x (dl x y)) := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : x ≠ dl y (dl x (dl x y)) := mod_symm nh
  have ef22 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef68 (X0 X1 : G) : X1 ◇ X0 = dl X0 (dl X0 X1) := by
    first | exact superpose ef22 ef17 | exact superpose ef17 ef22
  have ef200 : x ≠ dl y (y ◇ x) := by
    first | exact superpose ef68 ef18 | exact superpose ef18 ef68
  subsumption ef200 ef17

theorem Equation63_termStructuralFromFin_Equation125_finiteDivision :
    Law63.TermStructuralFromFin Law125 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj125R G _ M (Law125.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj125L G _ M (Law125.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law63.models_iff]
    exact fun x y ↦
      @aux125_63L G _ M (Law125.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 1692 `x = (y ◇ x) ◇ ((y ◇ x) ◇ y)` holds of the left division of any magma satisfying
equation 125 `x = y ◇ ((y ◇ x) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux125_1692L [Finite G] [Magma G] (h : Equation125 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl (dl y x) (dl (dl y x) y) := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : x ≠ dl (dl y x) (dl (dl y x) y) := mod_symm nh
  have ef22 (X0 X1 : G) : X1 ◇ (X0 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef68 (X0 X1 : G) : X1 ◇ X0 = dl X0 (dl X0 X1) := by
    first | exact superpose ef22 ef17 | exact superpose ef17 ef22
  have ef200 : x ≠ y ◇ (dl y x) := by
    first | exact superpose ef68 ef18 | exact superpose ef18 ef68
  subsumption ef200 ef16

theorem Equation1692_termStructuralFromFin_Equation125_finiteDivision :
    Law1692.TermStructuralFromFin Law125 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj125R G _ M (Law125.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj125L G _ M (Law125.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1692.models_iff]
    exact fun x y ↦
      @aux125_1692L G _ M (Law125.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 3954 `x ◇ y = (y ◇ (x ◇ y)) ◇ x` holds of the right division of any magma satisfying
equation 125 `x = y ◇ ((y ◇ x) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux125_3954R [Finite G] [Magma G] (h : Equation125 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x y = dr (dr y (dr x y)) x := by
  by_contra nh
  have hrot0 (a b : G) : b ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef12 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x y ≠ dr (dr y (dr x y)) x := mod_symm nh
  have ef30 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = dr X0 X1 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef137 (X0 X1 : G) : (dr X0 X1) ◇ X0 = dr X1 (dr X0 X1) := by
    first | exact superpose ef14 ef30 | exact superpose ef30 ef14
  have ef623 : dr x y ≠ dr ((dr x y) ◇ x) x := by
    first | exact superpose ef137 ef18 | exact superpose ef18 ef137
  subsumption ef623 ef15

theorem Equation3954_termStructuralFromFin_Equation125_finiteDivision :
    Law3954.TermStructuralFromFin Law125 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj125R G _ M (Law125.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj125L G _ M (Law125.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3954.models_iff]
    exact fun x y ↦
      @aux125_3954R G _ M (Law125.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 464
`x = y ◇ (x ◇ (x ◇ (x ◇ y)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj464R [Finite G] [Magma G] (h : Equation464 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ ((b ◇ a) ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (z ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef9 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef15 : t = (p ◇ t) ◇ ((p ◇ t) ◇ ((p ◇ t) ◇ q)) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef16 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1) = X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    first | exact superpose ef8 ef8
  have ef65 : (p ◇ t) ◇ ((p ◇ t) ◇ q) = t ◇ (t ◇ (t ◇ (p ◇ t))) := by
    first | exact superpose ef15 ef8 | exact superpose ef8 ef15
  have ef121 (X0 X1 : G) :
      (X1 ◇ X0) ◇ X1 = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇
      ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X1 ◇ X0))) := by
    first | exact superpose ef16 ef8 | exact superpose ef8 ef16
  have ef236 :
      (p ◇ t) ◇ q = (t ◇ (t ◇ (t ◇ (p ◇ t)))) ◇
      ((t ◇ (t ◇ (t ◇ (p ◇ t)))) ◇ ((t ◇ (t ◇ (t ◇ (p ◇ t)))) ◇ (p ◇ t))) := by
    first | exact superpose ef65 ef8 | exact superpose ef8 ef65
  have ef244 : (p ◇ t) ◇ q = (p ◇ t) ◇ p := by
    first | exact superpose ef121 ef236 | exact superpose ef236 ef121
  have ef296 : q = ((p ◇ t) ◇ p) ◇ (((p ◇ t) ◇ p) ◇ (((p ◇ t) ◇ p) ◇ (p ◇ t))) := by
    first | exact superpose ef244 ef8 | exact superpose ef8 ef244
  have ef308 : p = q := by
    first | exact superpose ef8 ef296 | exact superpose ef296 ef8
  subsumption ef308 ef10

/-- Left translation by `t` is injective in every finite magma satisfying equation 464
`x = y ◇ (x ◇ (x ◇ (x ◇ y)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj464L [Finite G] [Magma G] (h : Equation464 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ ((b ◇ a) ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (z ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef15 : q = (t ◇ p) ◇ ((t ◇ p) ◇ ((t ◇ p) ◇ t)) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef19 : p = q := by
    first | exact superpose ef8 ef15 | exact superpose ef15 ef8
  subsumption ef19 ef10

/-- Equation 511 `x = y ◇ (y ◇ (y ◇ (x ◇ y)))` holds of the left division of any magma satisfying
equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux464_511L [Finite G] [Magma G] (h : Equation464 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl y (dl y (dl y (dl x y))) := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl y (dl y (dl y (dl x y))) := mod_symm nh
  have ef24 (X0 X1 : G) : X0 ◇ (X0 ◇ (X0 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef101 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef24 ef15 | exact superpose ef15 ef24
  have ef492 : x ≠ dl y (dl y (y ◇ (y ◇ x))) := by
    first | exact superpose ef101 ef16 | exact superpose ef16 ef101
  have ef493 : x ≠ dl y (y ◇ x) := by
    first | exact superpose ef15 ef492 | exact superpose ef492 ef15
  subsumption ef493 ef15

theorem Equation511_termStructuralFromFin_Equation464_finiteDivision :
    Law511.TermStructuralFromFin Law464 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj464R G _ M (Law464.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj464L G _ M (Law464.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law511.models_iff]
    exact fun x y ↦
      @aux464_511L G _ M (Law464.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 614 `x = x ◇ (x ◇ ((x ◇ x) ◇ x))` holds of the left division of any magma satisfying
equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux464_614L [Finite G] [Magma G] (h : Equation464 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl x (dl x (dl (dl x x) x)) := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl x (dl (dl x x) x)) := mod_symm nh
  have ef20 (X0 X1 : G) : (dl X1 X0) ◇ (X1 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef63 (X0 X1 : G) : X0 ◇ (X0 ◇ X1) = dl (dl X0 X1) X0 := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef201 : x ≠ dl x (dl x (x ◇ (x ◇ x))) := by
    first | exact superpose ef63 ef16 | exact superpose ef16 ef63
  have ef202 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef15 ef201 | exact superpose ef201 ef15
  subsumption ef202 ef15

theorem Equation614_termStructuralFromFin_Equation464_finiteDivision :
    Law614.TermStructuralFromFin Law464 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj464R G _ M (Law464.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj464L G _ M (Law464.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law614.models_iff]
    exact fun x ↦
      @aux464_614L G _ M (Law464.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))` holds of the left division of any magma satisfying
equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux464_714L [Finite G] [Magma G] (h : Equation464 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl y (dl y (dl (dl y x) y)) := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl y (dl y (dl (dl y x) y)) := mod_symm nh
  have ef20 (X0 X1 : G) : (dl X1 X0) ◇ (X1 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef63 (X0 X1 : G) : X0 ◇ (X0 ◇ X1) = dl (dl X0 X1) X0 := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef197 : x ≠ dl y (dl y (y ◇ (y ◇ x))) := by
    first | exact superpose ef63 ef16 | exact superpose ef16 ef63
  have ef202 : x ≠ dl y (y ◇ x) := by
    first | exact superpose ef15 ef197 | exact superpose ef197 ef15
  subsumption ef202 ef15

theorem Equation714_termStructuralFromFin_Equation464_finiteDivision :
    Law714.TermStructuralFromFin Law464 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj464R G _ M (Law464.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj464L G _ M (Law464.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law714.models_iff]
    exact fun x y ↦
      @aux464_714L G _ M (Law464.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 1223 `x = x ◇ (((x ◇ x) ◇ x) ◇ x)` holds of the left division of any magma satisfying
equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux464_1223L [Finite G] [Magma G] (h : Equation464 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl x (dl (dl (dl x x) x) x) := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl (dl (dl x x) x) x) := mod_symm nh
  have ef20 (X0 X1 : G) : (dl X1 X0) ◇ (X1 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef24 (X0 X1 : G) : X0 ◇ (X0 ◇ (X0 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef63 (X0 X1 : G) : X0 ◇ (X0 ◇ X1) = dl (dl X0 X1) X0 := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef101 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef24 ef15 | exact superpose ef15 ef24
  have ef201 : x ≠ dl x (dl (x ◇ (x ◇ x)) x) := by
    first | exact superpose ef63 ef16 | exact superpose ef16 ef63
  have ef202 : x ≠ x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef101 ef201 | exact superpose ef201 ef101
  subsumption ef202 ef10

theorem Equation1223_termStructuralFromFin_Equation464_finiteDivision :
    Law1223.TermStructuralFromFin Law464 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj464R G _ M (Law464.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj464L G _ M (Law464.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1223.models_iff]
    exact fun x ↦
      @aux464_1223L G _ M (Law464.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 2238 `x = (x ◇ (x ◇ (x ◇ x))) ◇ x` holds of the left division of any magma satisfying
equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux464_2238L [Finite G] [Magma G] (h : Equation464 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl (dl x (dl x (dl x x))) x := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl (dl x (dl x (dl x x))) x := mod_symm nh
  have ef20 (X0 X1 : G) : (dl X1 X0) ◇ (X1 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef63 (X0 X1 : G) : X0 ◇ (X0 ◇ X1) = dl (dl X0 X1) X0 := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef197 : x ≠ x ◇ (x ◇ (dl x (dl x x))) := by
    first | exact superpose ef63 ef16 | exact superpose ef16 ef63
  have ef202 : x ≠ x ◇ (dl x x) := by
    first | exact superpose ef14 ef197 | exact superpose ef197 ef14
  subsumption ef202 ef14

theorem Equation2238_termStructuralFromFin_Equation464_finiteDivision :
    Law2238.TermStructuralFromFin Law464 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj464R G _ M (Law464.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj464L G _ M (Law464.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law2238.models_iff]
    exact fun x ↦
      @aux464_2238L G _ M (Law464.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 2338 `x = (y ◇ (y ◇ (y ◇ x))) ◇ y` holds of the left division of any magma satisfying
equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux464_2338L [Finite G] [Magma G] (h : Equation464 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl (dl y (dl y (dl y x))) y := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl (dl y (dl y (dl y x))) y := mod_symm nh
  have ef20 (X0 X1 : G) : (dl X1 X0) ◇ (X1 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef63 (X0 X1 : G) : X0 ◇ (X0 ◇ X1) = dl (dl X0 X1) X0 := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef197 : x ≠ y ◇ (y ◇ (dl y (dl y x))) := by
    first | exact superpose ef63 ef16 | exact superpose ef16 ef63
  have ef202 : x ≠ y ◇ (dl y x) := by
    first | exact superpose ef14 ef197 | exact superpose ef197 ef14
  subsumption ef202 ef14

theorem Equation2338_termStructuralFromFin_Equation464_finiteDivision :
    Law2338.TermStructuralFromFin Law464 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj464R G _ M (Law464.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj464L G _ M (Law464.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law2338.models_iff]
    exact fun x y ↦
      @aux464_2338L G _ M (Law464.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 2847 `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x` holds of the left division of any magma satisfying
equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux464_2847L [Finite G] [Magma G] (h : Equation464 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl (dl (dl x (dl x x)) x) x := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl (dl (dl x (dl x x)) x) x := mod_symm nh
  have ef20 (X0 X1 : G) : (dl X1 X0) ◇ (X1 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef24 (X0 X1 : G) : X0 ◇ (X0 ◇ (X0 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef63 (X0 X1 : G) : X0 ◇ (X0 ◇ X1) = dl (dl X0 X1) X0 := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef89 (X0 X1 : G) : X1 ◇ (dl X0 X1) = dl (X1 ◇ X0) X1 := by
    first | exact superpose ef24 ef24
  have ef197 : x ≠ dl (x ◇ (x ◇ (dl x x))) x := by
    first | exact superpose ef63 ef16 | exact superpose ef16 ef63
  have ef202 : x ≠ x ◇ (dl (x ◇ (dl x x)) x) := by
    first | exact superpose ef89 ef197 | exact superpose ef197 ef89
  have ef204 : x ≠ x ◇ (x ◇ (dl (dl x x) x)) := by
    first | exact superpose ef89 ef202 | exact superpose ef202 ef89
  have ef206 : x ≠ x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    first | exact superpose ef63 ef204 | exact superpose ef204 ef63
  subsumption ef206 ef10

theorem Equation2847_termStructuralFromFin_Equation464_finiteDivision :
    Law2847.TermStructuralFromFin Law464 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj464R G _ M (Law464.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj464L G _ M (Law464.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law2847.models_iff]
    exact fun x ↦
      @aux464_2847L G _ M (Law464.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 4380 `x ◇ (x ◇ x) = (x ◇ x) ◇ x` holds of the left division of any magma satisfying
equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux464_4380L [Finite G] [Magma G] (h : Equation464 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    dl x (dl x x) = dl (dl x x) x := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dl x (dl x x) ≠ dl (dl x x) x := mod_symm nh
  have ef20 (X0 X1 : G) : (dl X1 X0) ◇ (X1 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef24 (X0 X1 : G) : X0 ◇ (X0 ◇ (X0 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef63 (X0 X1 : G) : X0 ◇ (X0 ◇ X1) = dl (dl X0 X1) X0 := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef101 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef24 ef15 | exact superpose ef15 ef24
  have ef201 : dl x (dl x x) ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef63 ef16 | exact superpose ef16 ef63
  subsumption ef201 ef101

theorem Equation4380_termStructuralFromFin_Equation464_finiteDivision :
    Law4380.TermStructuralFromFin Law464 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj464R G _ M (Law464.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj464L G _ M (Law464.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4380.models_iff]
    exact fun x ↦
      @aux464_4380L G _ M (Law464.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 4435 `x ◇ (y ◇ x) = (x ◇ y) ◇ x` holds of the left division of any magma satisfying
equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux464_4435L [Finite G] [Magma G] (h : Equation464 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dl x (dl y x) = dl (dl x y) x := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dl x (dl y x) ≠ dl (dl x y) x := mod_symm nh
  have ef20 (X0 X1 : G) : (dl X1 X0) ◇ (X1 ◇ (X1 ◇ X0)) = X1 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef24 (X0 X1 : G) : X0 ◇ (X0 ◇ (X0 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef63 (X0 X1 : G) : X0 ◇ (X0 ◇ X1) = dl (dl X0 X1) X0 := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef101 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef24 ef15 | exact superpose ef15 ef24
  have ef197 : dl x (dl y x) ≠ x ◇ (x ◇ y) := by
    first | exact superpose ef63 ef16 | exact superpose ef16 ef63
  subsumption ef197 ef101

theorem Equation4435_termStructuralFromFin_Equation464_finiteDivision :
    Law4435.TermStructuralFromFin Law464 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj464R G _ M (Law464.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj464L G _ M (Law464.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4435.models_iff]
    exact fun x y ↦
      @aux464_4435L G _ M (Law464.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 467
`x = y ◇ (x ◇ (x ◇ (y ◇ y)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj467R [Finite G] [Magma G] (h : Equation467 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef9 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 : t = (p ◇ t) ◇ ((p ◇ t) ◇ (q ◇ q)) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef12 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ X1) = X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    first | exact superpose ef8 ef8
  have ef15 : (p ◇ t) ◇ (q ◇ q) = t ◇ (t ◇ ((p ◇ t) ◇ (p ◇ t))) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef16 : (p ◇ t) ◇ (q ◇ q) = (p ◇ t) ◇ (p ◇ p) := by
    first | exact superpose ef12 ef15 | exact superpose ef15 ef12
  have ef21 : q ◇ q = ((p ◇ t) ◇ (p ◇ p)) ◇ (((p ◇ t) ◇ (p ◇ p)) ◇ ((p ◇ t) ◇ (p ◇ t))) := by
    first | exact superpose ef16 ef8 | exact superpose ef8 ef16
  have ef22 : q ◇ q = p ◇ p := by
    first | exact superpose ef8 ef21 | exact superpose ef21 ef8
  have ef46 : q = (p ◇ p) ◇ ((p ◇ p) ◇ (p ◇ p)) := by
    first | exact superpose ef22 ef8 | exact superpose ef8 ef22
  have ef47 : p = q := by
    first | exact superpose ef8 ef46 | exact superpose ef46 ef8
  subsumption ef47 ef10

/-- Left translation by `t` is injective in every finite magma satisfying equation 467
`x = y ◇ (x ◇ (x ◇ (y ◇ y)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj467L [Finite G] [Magma G] (h : Equation467 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 : q = (t ◇ p) ◇ ((t ◇ p) ◇ (t ◇ t)) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef14 : p = q := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  subsumption ef14 ef10

/-- Equation 437 `x = x ◇ (y ◇ (y ◇ (x ◇ y)))` holds of the left division of any magma satisfying
equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux467_437L [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl y (dl y (dl x y))) := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl y (dl y (dl x y))) := mod_symm nh
  have ef20 (X0 X1 : G) : X0 ◇ (X0 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef42 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef78 : x ≠ dl x (dl y (y ◇ (x ◇ x))) := by
    first | exact superpose ef42 ef16 | exact superpose ef16 ef42
  have ef79 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef15 ef78 | exact superpose ef78 ef15
  subsumption ef79 ef15

theorem Equation437_termStructuralFromFin_Equation467_finiteDivision :
    Law437.TermStructuralFromFin Law467 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law437.models_iff]
    exact fun x y ↦
      @aux467_437L G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 477
`x = y ◇ (x ◇ (y ◇ (y ◇ y)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj477R [Finite G] [Magma G] (h : Equation477 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef9 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 : t = (p ◇ t) ◇ (q ◇ (q ◇ q)) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef12 (X0 X1 : G) : X1 ◇ (X1 ◇ X1) = X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    first | exact superpose ef8 ef8
  have ef16 : q ◇ (q ◇ q) = t ◇ ((p ◇ t) ◇ ((p ◇ t) ◇ (p ◇ t))) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef17 : q ◇ (q ◇ q) = p ◇ (p ◇ p) := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  have ef30 (X0 : G) : (q ◇ X0) ◇ (p ◇ (p ◇ p)) = X0 := by
    first | exact superpose ef17 ef8 | exact superpose ef8 ef17
  have ef33 : q ◇ q = (p ◇ (p ◇ p)) ◇ (p ◇ (p ◇ p)) := by
    first | exact superpose ef17 ef8 | exact superpose ef8 ef17
  have ef34 : q ◇ q = p ◇ p := by
    first | exact superpose ef8 ef33 | exact superpose ef33 ef8
  have ef78 : q = (p ◇ p) ◇ (p ◇ (p ◇ p)) := by
    first | exact superpose ef34 ef30 | exact superpose ef30 ef34
  have ef88 : p = q := by
    first | exact superpose ef8 ef78 | exact superpose ef78 ef8
  subsumption ef88 ef10

/-- Left translation by `t` is injective in every finite magma satisfying equation 477
`x = y ◇ (x ◇ (y ◇ (y ◇ y)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj477L [Finite G] [Magma G] (h : Equation477 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 : q = (t ◇ p) ◇ (t ◇ (t ◇ t)) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef15 : p = q := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  subsumption ef15 ef10

/-- Equation 417 `x = x ◇ (x ◇ (y ◇ (x ◇ y)))` holds of the left division of any magma satisfying
equation 477 `x = y ◇ (x ◇ (y ◇ (y ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux477_417L [Finite G] [Magma G] (h : Equation477 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl x (dl y (dl x y))) := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl x (dl y (dl x y))) := mod_symm nh
  have ef20 (X0 X1 : G) : X0 ◇ (X1 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef51 (X0 X1 : G) : X0 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef146 : x ≠ dl x (dl x (x ◇ (x ◇ x))) := by
    first | exact superpose ef51 ef16 | exact superpose ef16 ef51
  have ef147 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef15 ef146 | exact superpose ef146 ef15
  subsumption ef147 ef15

theorem Equation417_termStructuralFromFin_Equation477_finiteDivision :
    Law417.TermStructuralFromFin Law477 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj477R G _ M (Law477.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj477L G _ M (Law477.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law417.models_iff]
    exact fun x y ↦
      @aux477_417L G _ M (Law477.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` holds of the left division of any magma satisfying
equation 477 `x = y ◇ (x ◇ (y ◇ (y ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux477_4273L [Finite G] [Magma G] (h : Equation477 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dl x (dl x x) = dl y (dl x y) := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dl x (dl x x) ≠ dl y (dl x y) := mod_symm nh
  have ef20 (X0 X1 : G) : X0 ◇ (X1 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef51 (X0 X1 : G) : X0 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef146 : dl x (dl x x) ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef51 ef16 | exact superpose ef16 ef51
  subsumption ef146 ef51

theorem Equation4273_termStructuralFromFin_Equation477_finiteDivision :
    Law4273.TermStructuralFromFin Law477 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj477R G _ M (Law477.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj477L G _ M (Law477.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4273.models_iff]
    exact fun x y ↦
      @aux477_4273L G _ M (Law477.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 3112 `x = (((y ◇ x) ◇ y) ◇ x) ◇ x` holds of the right division of any magma satisfying
equation 477 `x = y ◇ (x ◇ (y ◇ (y ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux477_3112R [Finite G] [Magma G] (h : Equation477 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dr (dr (dr (dr y x) y) x) x := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dr (dr (dr (dr y x) y) x) x := mod_symm nh
  have ef18 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef12 ef15 | exact superpose ef15 ef12
  have ef19 (X0 X1 : G) : X1 ◇ X0 = dr X0 (X1 ◇ (X1 ◇ X1)) := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef20 (X0 X1 : G) : X0 ◇ (X1 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef21 (X0 X1 : G) : dr X0 (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X1 := by
    first | exact superpose ef10 ef13 | exact superpose ef13 ef10
  have ef29 (X0 X1 : G) : X1 ◇ (X1 ◇ X1) = dl (X1 ◇ X0) X0 := by
    first | exact superpose ef11 ef15 | exact superpose ef15 ef11
  have ef51 (X0 X1 : G) : X0 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef74 (X0 X1 X2 : G) : dl (X0 ◇ X1) X1 = dl (X0 ◇ X2) X2 := by
    first | exact superpose ef29 ef29
  have ef77 (X0 X1 : G) : X1 ◇ (X1 ◇ X1) = dl (dl X0 X1) (X0 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef20 ef29 | exact superpose ef29 ef20
  have ef82 (X0 X1 X2 : G) : X0 ◇ X2 = dr X2 (dl (X0 ◇ X1) X1) := by
    first | exact superpose ef29 ef19 | exact superpose ef19 ef29
  have ef136 (X0 X1 X2 : G) : dr X2 (X2 ◇ (dl X0 (dl X1 X0))) = X1 := by
    first | exact superpose ef51 ef21 | exact superpose ef21 ef51
  have ef180 (X0 X1 X2 : G) : dl X0 X1 = dl ((dr X0 X1) ◇ X2) X2 := by
    first | exact superpose ef12 ef74 | exact superpose ef74 ef12
  have ef254 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = dr X2 (dl X0 X1) := by
    first | exact superpose ef12 ef82 | exact superpose ef82 ef12
  have ef852 (X0 X1 X2 : G) : dr X2 X0 = dr X1 (X1 ◇ (dl X2 X0)) := by
    first | exact superpose ef18 ef136 | exact superpose ef136 ef18
  have ef1668 (X0 X1 X2 : G) : dl X1 X2 = dl (dl X0 (dr X1 X2)) (X0 ◇ (X0 ◇ X0)) := by
    first | exact superpose ef20 ef180 | exact superpose ef180 ef20
  have ef1966 (X0 X1 X2 : G) : dr X2 X0 = (dr X1 (X1 ◇ X0)) ◇ X2 := by
    first | exact superpose ef15 ef254 | exact superpose ef254 ef15
  have ef3758 (X0 X1 X2 : G) : dr (dr X1 X0) X1 = dr X2 (X2 ◇ X0) := by
    first | exact superpose ef18 ef852 | exact superpose ef852 ef18
  have ef4577 (X0 X1 X2 : G) :
      dr ((dr X0 (X0 ◇ X1)) ◇ (dr X0 (X0 ◇ X1))) X1 =
      dl (dl X2 (dr X0 (X0 ◇ X1))) (X2 ◇ (X2 ◇ X2)) := by
    first | exact superpose ef1966 ef77 | exact superpose ef77 ef1966
  have ef4617 (X0 X1 : G) : dl X0 (X0 ◇ X1) = dr ((dr X0 (X0 ◇ X1)) ◇ (dr X0 (X0 ◇ X1))) X1 := by
    first | exact superpose ef1668 ef4577 | exact superpose ef4577 ef1668
  have ef4723 (X0 X1 : G) : dl X0 (X0 ◇ X1) = dr (dr (dr X0 (X0 ◇ X1)) X1) X1 := by
    first | exact superpose ef1966 ef4617 | exact superpose ef4617 ef1966
  have ef4796 (X0 X1 : G) : dr (dr (dr X0 (X0 ◇ X1)) X1) X1 = X1 := by
    first | exact superpose ef15 ef4723 | exact superpose ef4723 ef15
  have ef7726 (X0 : G) : x ≠ dr (dr (dr X0 (X0 ◇ x)) x) x := by
    first | exact superpose ef3758 ef16 | exact superpose ef16 ef3758
  subsumption ef7726 ef4796

theorem Equation3112_termStructuralFromFin_Equation477_finiteDivision :
    Law3112.TermStructuralFromFin Law477 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj477R G _ M (Law477.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj477L G _ M (Law477.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3112.models_iff]
    exact fun x y ↦
      @aux477_3112R G _ M (Law477.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4588 `(x ◇ x) ◇ x = (y ◇ x) ◇ y` holds of the right division of any magma satisfying
equation 477 `x = y ◇ (x ◇ (y ◇ (y ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux477_4588R [Finite G] [Magma G] (h : Equation477 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr (dr x x) x = dr (dr y x) y := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dr (dr x x) x ≠ dr (dr y x) y := mod_symm nh
  have ef18 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef12 ef15 | exact superpose ef15 ef12
  have ef20 (X0 X1 : G) : X0 ◇ (X1 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef21 (X0 X1 : G) : dr X0 (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X1 := by
    first | exact superpose ef10 ef13 | exact superpose ef13 ef10
  have ef51 (X0 X1 : G) : X0 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef136 (X0 X1 X2 : G) : dr X2 (X2 ◇ (dl X0 (dl X1 X0))) = X1 := by
    first | exact superpose ef51 ef21 | exact superpose ef21 ef51
  have ef852 (X0 X1 X2 : G) : dr X2 X0 = dr X1 (X1 ◇ (dl X2 X0)) := by
    first | exact superpose ef18 ef136 | exact superpose ef136 ef18
  have ef3758 (X0 X1 X2 : G) : dr (dr X1 X0) X1 = dr X2 (X2 ◇ X0) := by
    first | exact superpose ef18 ef852 | exact superpose ef852 ef18
  have ef7726 (X0 : G) : dr (dr x x) x ≠ dr X0 (X0 ◇ x) := by
    first | exact superpose ef3758 ef16 | exact superpose ef16 ef3758
  subsumption ef7726 ef3758

theorem Equation4588_termStructuralFromFin_Equation477_finiteDivision :
    Law4588.TermStructuralFromFin Law477 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj477R G _ M (Law477.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj477L G _ M (Law477.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4588.models_iff]
    exact fun x y ↦
      @aux477_4588R G _ M (Law477.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 481
`x = y ◇ (x ◇ (y ◇ (z ◇ z)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj481R [Finite G] [Magma G] (h : Equation481 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ a) ◇ (b ◇ (c ◇ c)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (c ◇ c)))
      (fun z ↦ (h z b c).symm) a
  have ef7 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (hrot0 ..)
  have ef9 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef19 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef74 (X0 : G) : q = ((X0 ◇ X0) ◇ t) ◇ (p ◇ t) := by
    first | exact superpose ef9 ef19 | exact superpose ef19 ef9
  have ef98 : p = q := by
    first | exact superpose ef19 ef74 | exact superpose ef74 ef19
  subsumption ef98 ef10

/-- Left translation by `t` is injective in every finite magma satisfying equation 481
`x = y ◇ (x ◇ (y ◇ (z ◇ z)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj481L [Finite G] [Magma G] (h : Equation481 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ a) ◇ (b ◇ (c ◇ c)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (c ◇ c)))
      (fun z ↦ (h z b c).symm) a
  have ef8 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef13 (X0 : G) : q = (t ◇ p) ◇ (t ◇ (X0 ◇ X0)) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef21 : p = q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef21 ef10

/-- Equation 417 `x = x ◇ (x ◇ (y ◇ (x ◇ y)))` holds of the left division of any magma satisfying
equation 481 `x = y ◇ (x ◇ (y ◇ (z ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux481_417L [Finite G] [Magma G] (h : Equation481 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl x (dl y (dl x y))) := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl x (dl y (dl x y))) := mod_symm nh
  have ef22 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef10 ef10
  have ef23 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (X2 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef62 (X0 X1 : G) : dl X1 (X0 ◇ X0) = X1 := by
    first | exact superpose ef22 ef15 | exact superpose ef15 ef22
  have ef159 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X2) = dl X1 (dl X0 X1) := by
    first | exact superpose ef23 ef15 | exact superpose ef15 ef23
  have ef2280 (X0 : G) : x ≠ dl x (dl x (x ◇ (X0 ◇ X0))) := by
    first | exact superpose ef159 ef16 | exact superpose ef16 ef159
  have ef2281 (X0 : G) : x ≠ dl x (X0 ◇ X0) := by
    first | exact superpose ef15 ef2280 | exact superpose ef2280 ef15
  subsumption ef2281 ef62

theorem Equation417_termStructuralFromFin_Equation481_finiteDivision :
    Law417.TermStructuralFromFin Law481 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj481R G _ M (Law481.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj481L G _ M (Law481.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law417.models_iff]
    exact fun x y ↦
      @aux481_417L G _ M (Law481.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 429 `x = x ◇ (y ◇ (x ◇ (y ◇ x)))` holds of the left division of any magma satisfying
equation 481 `x = y ◇ (x ◇ (y ◇ (z ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux481_429L [Finite G] [Magma G] (h : Equation481 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl y (dl x (dl y x))) := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl y (dl x (dl y x))) := mod_symm nh
  have ef22 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef10 ef10
  have ef23 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (X2 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef62 (X0 X1 : G) : dl X1 (X0 ◇ X0) = X1 := by
    first | exact superpose ef22 ef15 | exact superpose ef15 ef22
  have ef159 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X2) = dl X1 (dl X0 X1) := by
    first | exact superpose ef23 ef15 | exact superpose ef15 ef23
  have ef2280 (X0 : G) : x ≠ dl x (dl y (y ◇ (X0 ◇ X0))) := by
    first | exact superpose ef159 ef16 | exact superpose ef16 ef159
  have ef2281 (X0 : G) : x ≠ dl x (X0 ◇ X0) := by
    first | exact superpose ef15 ef2280 | exact superpose ef2280 ef15
  subsumption ef2281 ef62

theorem Equation429_termStructuralFromFin_Equation481_finiteDivision :
    Law429.TermStructuralFromFin Law481 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj481R G _ M (Law481.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj481L G _ M (Law481.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law429.models_iff]
    exact fun x y ↦
      @aux481_429L G _ M (Law481.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 440 `x = x ◇ (y ◇ (y ◇ (y ◇ y)))` holds of the left division of any magma satisfying
equation 481 `x = y ◇ (x ◇ (y ◇ (z ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux481_440L [Finite G] [Magma G] (h : Equation481 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl y (dl y (dl y y))) := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl y (dl y (dl y y))) := mod_symm nh
  have ef22 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef10 ef10
  have ef23 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (X2 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef62 (X0 X1 : G) : dl X1 (X0 ◇ X0) = X1 := by
    first | exact superpose ef22 ef15 | exact superpose ef15 ef22
  have ef159 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X2) = dl X1 (dl X0 X1) := by
    first | exact superpose ef23 ef15 | exact superpose ef15 ef23
  have ef2280 (X0 : G) : x ≠ dl x (dl y (y ◇ (X0 ◇ X0))) := by
    first | exact superpose ef159 ef16 | exact superpose ef16 ef159
  have ef2281 (X0 : G) : x ≠ dl x (X0 ◇ X0) := by
    first | exact superpose ef15 ef2280 | exact superpose ef2280 ef15
  subsumption ef2281 ef62

theorem Equation440_termStructuralFromFin_Equation481_finiteDivision :
    Law440.TermStructuralFromFin Law481 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj481R G _ M (Law481.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj481L G _ M (Law481.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law440.models_iff]
    exact fun x y ↦
      @aux481_440L G _ M (Law481.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 452 `x = x ◇ (y ◇ (z ◇ (y ◇ z)))` holds of the left division of any magma satisfying
equation 481 `x = y ◇ (x ◇ (y ◇ (z ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux481_452L [Finite G] [Magma G] (h : Equation481 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    x = dl x (dl y (dl z (dl y z))) := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl y (dl z (dl y z))) := mod_symm nh
  have ef22 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef10 ef10
  have ef23 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (X2 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef62 (X0 X1 : G) : dl X1 (X0 ◇ X0) = X1 := by
    first | exact superpose ef22 ef15 | exact superpose ef15 ef22
  have ef159 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X2) = dl X1 (dl X0 X1) := by
    first | exact superpose ef23 ef15 | exact superpose ef15 ef23
  have ef2280 (X0 : G) : x ≠ dl x (dl y (y ◇ (X0 ◇ X0))) := by
    first | exact superpose ef159 ef16 | exact superpose ef16 ef159
  have ef2281 (X0 : G) : x ≠ dl x (X0 ◇ X0) := by
    first | exact superpose ef15 ef2280 | exact superpose ef2280 ef15
  subsumption ef2281 ef62

theorem Equation452_termStructuralFromFin_Equation481_finiteDivision :
    Law452.TermStructuralFromFin Law481 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj481R G _ M (Law481.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj481L G _ M (Law481.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law452.models_iff]
    exact fun x y z ↦
      @aux481_452L G _ M (Law481.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` holds of the left division of any magma satisfying
equation 481 `x = y ◇ (x ◇ (y ◇ (z ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux481_4273L [Finite G] [Magma G] (h : Equation481 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dl x (dl x x) = dl y (dl x y) := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dl x (dl x x) ≠ dl y (dl x y) := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (X2 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef159 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X2) = dl X1 (dl X0 X1) := by
    first | exact superpose ef23 ef15 | exact superpose ef15 ef23
  have ef2280 (X0 : G) : dl x (dl x x) ≠ x ◇ (X0 ◇ X0) := by
    first | exact superpose ef159 ef16 | exact superpose ef16 ef159
  subsumption ef2280 ef159

theorem Equation4273_termStructuralFromFin_Equation481_finiteDivision :
    Law4273.TermStructuralFromFin Law481 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj481R G _ M (Law481.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj481L G _ M (Law481.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4273.models_iff]
    exact fun x y ↦
      @aux481_4273L G _ M (Law481.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 3068 `x = (((x ◇ y) ◇ x) ◇ y) ◇ x` holds of the right division of any magma satisfying
equation 481 `x = y ◇ (x ◇ (y ◇ (z ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux481_3068R [Finite G] [Magma G] (h : Equation481 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dr (dr (dr (dr x y) x) y) x := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 : x ≠ dr (dr (dr (dr x y) x) y) x := mod_symm nh
  have ef19 (X0 X1 X2 : G) : (dr X0 (X1 ◇ X1)) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef22 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef10 ef10
  have ef63 (X0 X1 : G) : dr (X0 ◇ X0) X1 = X1 := by
    first | exact superpose ef22 ef13 | exact superpose ef13 ef22
  have ef83 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 (X2 ◇ X2)) ◇ X0 := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef824 (X0 X1 X2 : G) : dr (dr (dr X0 (X1 ◇ X1)) X0) X2 = X2 := by
    first | exact superpose ef83 ef63 | exact superpose ef63 ef83
  have ef835 (X0 X1 X2 : G) : dr X1 (X2 ◇ X2) = dr (dr X0 X1) X0 := by
    first | exact superpose ef83 ef13 | exact superpose ef13 ef83
  have ef10312 (X0 : G) : x ≠ dr (dr (dr y (X0 ◇ X0)) y) x := by
    first | exact superpose ef835 ef16 | exact superpose ef16 ef835
  subsumption ef10312 ef824

theorem Equation3068_termStructuralFromFin_Equation481_finiteDivision :
    Law3068.TermStructuralFromFin Law481 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj481R G _ M (Law481.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj481L G _ M (Law481.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3068.models_iff]
    exact fun x y ↦
      @aux481_3068R G _ M (Law481.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 3112 `x = (((y ◇ x) ◇ y) ◇ x) ◇ x` holds of the right division of any magma satisfying
equation 481 `x = y ◇ (x ◇ (y ◇ (z ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux481_3112R [Finite G] [Magma G] (h : Equation481 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dr (dr (dr (dr y x) y) x) x := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 : x ≠ dr (dr (dr (dr y x) y) x) x := mod_symm nh
  have ef19 (X0 X1 X2 : G) : (dr X0 (X1 ◇ X1)) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef22 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef10 ef10
  have ef63 (X0 X1 : G) : dr (X0 ◇ X0) X1 = X1 := by
    first | exact superpose ef22 ef13 | exact superpose ef13 ef22
  have ef83 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 (X2 ◇ X2)) ◇ X0 := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef824 (X0 X1 X2 : G) : dr (dr (dr X0 (X1 ◇ X1)) X0) X2 = X2 := by
    first | exact superpose ef83 ef63 | exact superpose ef63 ef83
  have ef835 (X0 X1 X2 : G) : dr X1 (X2 ◇ X2) = dr (dr X0 X1) X0 := by
    first | exact superpose ef83 ef13 | exact superpose ef13 ef83
  have ef10312 (X0 : G) : x ≠ dr (dr (dr x (X0 ◇ X0)) x) x := by
    first | exact superpose ef835 ef16 | exact superpose ef16 ef835
  subsumption ef10312 ef824

theorem Equation3112_termStructuralFromFin_Equation481_finiteDivision :
    Law3112.TermStructuralFromFin Law481 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj481R G _ M (Law481.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj481L G _ M (Law481.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3112.models_iff]
    exact fun x y ↦
      @aux481_3112R G _ M (Law481.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 3152 `x = (((y ◇ y) ◇ y) ◇ y) ◇ x` holds of the right division of any magma satisfying
equation 481 `x = y ◇ (x ◇ (y ◇ (z ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux481_3152R [Finite G] [Magma G] (h : Equation481 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dr (dr (dr (dr y y) y) y) x := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 : x ≠ dr (dr (dr (dr y y) y) y) x := mod_symm nh
  have ef19 (X0 X1 X2 : G) : (dr X0 (X1 ◇ X1)) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef22 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef10 ef10
  have ef63 (X0 X1 : G) : dr (X0 ◇ X0) X1 = X1 := by
    first | exact superpose ef22 ef13 | exact superpose ef13 ef22
  have ef83 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 (X2 ◇ X2)) ◇ X0 := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef824 (X0 X1 X2 : G) : dr (dr (dr X0 (X1 ◇ X1)) X0) X2 = X2 := by
    first | exact superpose ef83 ef63 | exact superpose ef63 ef83
  have ef835 (X0 X1 X2 : G) : dr X1 (X2 ◇ X2) = dr (dr X0 X1) X0 := by
    first | exact superpose ef83 ef13 | exact superpose ef13 ef83
  have ef10330 (X0 : G) : x ≠ dr (dr (dr y (X0 ◇ X0)) y) x := by
    first | exact superpose ef835 ef16 | exact superpose ef16 ef835
  subsumption ef10330 ef824

theorem Equation3152_termStructuralFromFin_Equation481_finiteDivision :
    Law3152.TermStructuralFromFin Law481 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj481R G _ M (Law481.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj481L G _ M (Law481.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3152.models_iff]
    exact fun x y ↦
      @aux481_3152R G _ M (Law481.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 3201 `x = (((y ◇ z) ◇ y) ◇ z) ◇ x` holds of the right division of any magma satisfying
equation 481 `x = y ◇ (x ◇ (y ◇ (z ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux481_3201R [Finite G] [Magma G] (h : Equation481 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    x = dr (dr (dr (dr y z) y) z) x := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 : x ≠ dr (dr (dr (dr y z) y) z) x := mod_symm nh
  have ef19 (X0 X1 X2 : G) : (dr X0 (X1 ◇ X1)) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef22 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef10 ef10
  have ef63 (X0 X1 : G) : dr (X0 ◇ X0) X1 = X1 := by
    first | exact superpose ef22 ef13 | exact superpose ef13 ef22
  have ef83 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 (X2 ◇ X2)) ◇ X0 := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef824 (X0 X1 X2 : G) : dr (dr (dr X0 (X1 ◇ X1)) X0) X2 = X2 := by
    first | exact superpose ef83 ef63 | exact superpose ef63 ef83
  have ef835 (X0 X1 X2 : G) : dr X1 (X2 ◇ X2) = dr (dr X0 X1) X0 := by
    first | exact superpose ef83 ef13 | exact superpose ef13 ef83
  have ef10312 (X0 : G) : x ≠ dr (dr (dr z (X0 ◇ X0)) z) x := by
    first | exact superpose ef835 ef16 | exact superpose ef16 ef835
  subsumption ef10312 ef824

theorem Equation3201_termStructuralFromFin_Equation481_finiteDivision :
    Law3201.TermStructuralFromFin Law481 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj481R G _ M (Law481.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj481L G _ M (Law481.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3201.models_iff]
    exact fun x y z ↦
      @aux481_3201R G _ M (Law481.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Equation 4588 `(x ◇ x) ◇ x = (y ◇ x) ◇ y` holds of the right division of any magma satisfying
equation 481 `x = y ◇ (x ◇ (y ◇ (z ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux481_4588R [Finite G] [Magma G] (h : Equation481 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr (dr x x) x = dr (dr y x) y := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 : dr (dr x x) x ≠ dr (dr y x) y := mod_symm nh
  have ef19 (X0 X1 X2 : G) : (dr X0 (X1 ◇ X1)) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef83 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 (X2 ◇ X2)) ◇ X0 := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef835 (X0 X1 X2 : G) : dr X1 (X2 ◇ X2) = dr (dr X0 X1) X0 := by
    first | exact superpose ef83 ef13 | exact superpose ef13 ef83
  have ef10308 (X0 : G) : dr (dr x x) x ≠ dr x (X0 ◇ X0) := by
    first | exact superpose ef835 ef16 | exact superpose ef16 ef835
  subsumption ef10308 ef835

theorem Equation4588_termStructuralFromFin_Equation481_finiteDivision :
    Law4588.TermStructuralFromFin Law481 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj481R G _ M (Law481.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj481L G _ M (Law481.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4588.models_iff]
    exact fun x y ↦
      @aux481_4588R G _ M (Law481.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 546
`x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj546R [Finite G] [Magma G] (h : Equation546 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef11 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef16 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := by
    first | exact superpose ef8 ef8
  have ef25 : q = (p ◇ t) ◇ t := by
    first | exact superpose ef11 ef16 | exact superpose ef16 ef11
  have ef35 : p = q := by
    first | exact superpose ef16 ef25 | exact superpose ef25 ef16
  subsumption ef35 ef12

/-- Left translation by `t` is injective in every finite magma satisfying equation 546
`x = y ◇ (z ◇ (x ◇ (z ◇ y)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj546L [Finite G] [Magma G] (h : Equation546 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ (h z b c).symm) a
  have ef9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef17 (X0 : G) : q = (X0 ◇ (t ◇ p)) ◇ (t ◇ X0) := by
    first | exact superpose ef11 ef9 | exact superpose ef9 ef11
  have ef25 : p = q := by
    first | exact superpose ef9 ef17 | exact superpose ef17 ef9
  subsumption ef25 ef12

/-- Equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))` holds of the left division of any magma satisfying
equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))` and equipped with two-sided divisions. -/
private theorem aux546_556L [Finite G] [Magma G] (h : Equation546 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    x = dl y (dl z (dl y (dl x z))) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : x ≠ dl y (dl z (dl y (dl x z))) := mod_symm nh
  have ef22 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef26 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = X1 := by
    first | exact superpose ef11 ef11
  have ef27 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ (X2 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef81 (X0 X1 : G) : X0 ◇ (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef26 | exact superpose ef26 ef16
  have ef93 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X1) = X1 ◇ (X2 ◇ X0) := by
    first | exact superpose ef26 ef11 | exact superpose ef11 ef26
  have ef212 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ X3) = (X1 ◇ X0) ◇ ((dl X2 X3) ◇ X1) := by
    first | exact superpose ef22 ef12 | exact superpose ef12 ef22
  have ef222 (X0 X1 X2 X3 : G) : X2 ◇ (X0 ◇ X3) = X1 ◇ ((dl X2 X3) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef93 ef212 | exact superpose ef212 ef93
  have ef237 (X0 X2 X3 : G) : X2 ◇ (X0 ◇ X3) = dl X0 (dl X2 X3) := by
    first | exact superpose ef27 ef222 | exact superpose ef222 ef27
  have ef4809 : x ≠ dl y (y ◇ (z ◇ (dl x z))) := by
    first | exact superpose ef237 ef18 | exact superpose ef18 ef237
  have ef4810 : x ≠ z ◇ (dl x z) := by
    first | exact superpose ef17 ef4809 | exact superpose ef4809 ef17
  subsumption ef4810 ef81

theorem Equation556_termStructuralFromFin_Equation546_finiteDivision :
    Law556.TermStructuralFromFin Law546 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj546R G _ M (Law546.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj546L G _ M (Law546.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law556.models_iff]
    exact fun x y z ↦
      @aux546_556L G _ M (Law546.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Right translation by `t` is injective in every finite magma satisfying equation 556
`x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj556R [Finite G] [Magma G] (h : Equation556 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have ef9 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef13 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef14 : p ≠ q := mod_symm nh
  have ef15 (X0 : G) : q = X0 ◇ (t ◇ (X0 ◇ (p ◇ t))) := by
    first | exact superpose ef13 ef9 | exact superpose ef9 ef13
  have ef19 : p = q := by
    first | exact superpose ef9 ef15 | exact superpose ef15 ef9
  subsumption ef19 ef14

/-- Left translation by `t` is injective in every finite magma satisfying equation 556
`x = y ◇ (z ◇ (y ◇ (x ◇ z)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj556L [Finite G] [Magma G] (h : Equation556 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ (b ◇ a))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ (b ◇ z))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : b ◇ ((b ◇ (c ◇ a)) ◇ c) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (c ◇ z)) ◇ c) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b c) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (hrot1 ..)
  have ef13 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef14 : p ≠ q := mod_symm nh
  have ef46 (X0 : G) : q = X0 ◇ ((X0 ◇ (t ◇ p)) ◇ t) := by
    first | exact superpose ef13 ef11 | exact superpose ef11 ef13
  have ef73 : p = q := by
    first | exact superpose ef11 ef46 | exact superpose ef46 ef11
  subsumption ef73 ef14

/-- Equation 546 `x = y ◇ (z ◇ (x ◇ (z ◇ y)))` holds of the left division of any magma satisfying
equation 556 `x = y ◇ (z ◇ (y ◇ (x ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux556_546L [Finite G] [Magma G] (h : Equation556 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    x = dl y (dl z (dl x (dl z y))) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ (b ◇ a))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ (b ◇ z))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : b ◇ ((b ◇ (c ◇ a)) ◇ c) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (c ◇ z)) ◇ c) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot0 z b c) a
  have ef12 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2) = X0 := mod_symm (hrot1 ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 : x ≠ dl y (dl z (dl x (dl z y))) := mod_symm nh
  have ef23 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X1 ◇ X0)) = dr X0 X2 := by
    first | exact superpose ef16 ef12 | exact superpose ef12 ef16
  have ef28 (X0 X1 : G) : X1 ◇ X0 = X0 ◇ X1 := by
    first | exact superpose ef12 ef12
  have ef62 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ X0) ◇ X2) = dl X2 X0 := by
    first | exact superpose ef18 ef14 | exact superpose ef14 ef18
  have ef64 (X0 X1 X2 X3 : G) : X1 ◇ ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X3 ◇ X0)) ◇ X3 := by
    first | exact superpose ef14 ef14
  have ef85 (X0 X1 X2 X3 : G) : X1 ◇ ((X1 ◇ X0) ◇ X2) = X3 ◇ (X2 ◇ (X3 ◇ X0)) := by
    first | exact superpose ef28 ef64 | exact superpose ef64 ef28
  have ef95 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ X0) ◇ X2) = dr X0 X2 := by
    first | exact superpose ef23 ef85 | exact superpose ef85 ef23
  have ef98 (X0 X2 : G) : dr X0 X2 = dl X2 X0 := by
    first | exact superpose ef62 ef95 | exact superpose ef95 ef62
  have ef287 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dl X2 (dr X0 X1) := by
    first | exact superpose ef23 ef19 | exact superpose ef19 ef23
  have ef292 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dl X2 (dl X1 X0) := by
    first | exact superpose ef98 ef287 | exact superpose ef287 ef98
  have ef1845 : x ≠ z ◇ (y ◇ (dl x (dl z y))) := by
    first | exact superpose ef292 ef20 | exact superpose ef20 ef292
  have ef1848 : x ≠ z ◇ (y ◇ (z ◇ (x ◇ y))) := by
    first | exact superpose ef292 ef1845 | exact superpose ef1845 ef292
  subsumption ef1848 ef12

theorem Equation546_termStructuralFromFin_Equation556_finiteDivision :
    Law546.TermStructuralFromFin Law556 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj556R G _ M (Law556.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj556L G _ M (Law556.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law546.models_iff]
    exact fun x y z ↦
      @aux556_546L G _ M (Law556.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Right translation by `t` is injective in every finite magma satisfying equation 714
`x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj714R [Finite G] [Magma G] (h : Equation714 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : b ◇ (b ◇ (b ◇ (a ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ (z ◇ b))) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef10 (X0 X1 : G) : X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (hrot0 ..)
  have ef13 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef14 : p ≠ q := mod_symm nh
  have ef17 : q = t ◇ (t ◇ (t ◇ (p ◇ t))) := by
    first | exact superpose ef13 ef10 | exact superpose ef10 ef13
  have ef21 : p = q := by
    first | exact superpose ef10 ef17 | exact superpose ef17 ef10
  subsumption ef21 ef14

/-- Left translation by `t` is injective in every finite magma satisfying equation 714
`x = y ◇ (y ◇ ((y ◇ x) ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj714L [Finite G] [Magma G] (h : Equation714 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have ef9 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef14 : p ≠ q := mod_symm nh
  have ef15 : q = t ◇ (t ◇ ((t ◇ p) ◇ t)) := by
    first | exact superpose ef13 ef9 | exact superpose ef9 ef13
  have ef17 : p = q := by
    first | exact superpose ef9 ef15 | exact superpose ef15 ef9
  subsumption ef17 ef14

/-- Equation 464 `x = y ◇ (x ◇ (x ◇ (x ◇ y)))` holds of the left division of any magma satisfying
equation 714 `x = y ◇ (y ◇ ((y ◇ x) ◇ y))` and equipped with two-sided divisions. -/
private theorem aux714_464L [Finite G] [Magma G] (h : Equation714 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl y (dl x (dl x (dl x y))) := by
  by_contra nh
  have hrot0 (a b : G) : b ◇ (b ◇ (b ◇ (a ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ (z ◇ b))) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : (b ◇ (b ◇ (b ◇ a))) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ (b ◇ z))) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have hrot2 (a b : G) : b ◇ ((b ◇ (b ◇ a)) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot1 z b) a
  have ef12 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef15 (X0 X1 : G) : X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (hrot2 ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 : x ≠ dl y (dl x (dl x (dl x y))) := mod_symm nh
  have ef24 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef18 ef12 | exact superpose ef12 ef18
  have ef95 (X0 X1 : G) : X1 ◇ X0 = X0 ◇ ((dl X0 X1) ◇ X0) := by
    first | exact superpose ef24 ef15 | exact superpose ef15 ef24
  have ef102 (X0 X1 : G) : X0 ◇ (X1 ◇ X0) = dl X0 (dl X0 X1) := by
    first | exact superpose ef24 ef19 | exact superpose ef19 ef24
  have ef423 : x ≠ dl y (x ◇ ((dl x y) ◇ x)) := by
    first | exact superpose ef102 ef20 | exact superpose ef20 ef102
  have ef424 : x ≠ dl y (y ◇ x) := by
    first | exact superpose ef95 ef423 | exact superpose ef423 ef95
  subsumption ef424 ef19

theorem Equation464_termStructuralFromFin_Equation714_finiteDivision :
    Law464.TermStructuralFromFin Law714 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj714R G _ M (Law714.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj714L G _ M (Law714.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law464.models_iff]
    exact fun x y ↦
      @aux714_464L G _ M (Law714.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 1276
`x = y ◇ (((x ◇ x) ◇ x) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1276R [Finite G] [Magma G] (h : Equation1276 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ (a ◇ b)) ◇ (b ◇ (a ◇ b))) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ (z ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef9 (X0 X1 : G) :
      ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef11 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef18 : q = ((t ◇ (p ◇ t)) ◇ (t ◇ (p ◇ t))) ◇ (t ◇ (p ◇ t)) := by
    first | exact superpose ef11 ef9 | exact superpose ef9 ef11
  have ef26 : p = q := by
    first | exact superpose ef9 ef18 | exact superpose ef18 ef9
  subsumption ef26 ef12

/-- Left translation by `t` is injective in every finite magma satisfying equation 1276
`x = y ◇ (((x ◇ x) ◇ x) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1276L [Finite G] [Magma G] (h : Equation1276 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ (a ◇ b)) ◇ (b ◇ (a ◇ b))) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ (z ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : (((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ ((b ◇ z) ◇ (b ◇ z)) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef10 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef14 : q = (((t ◇ p) ◇ (t ◇ p)) ◇ (t ◇ p)) ◇ t := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef16 : p = q := by
    first | exact superpose ef10 ef14 | exact superpose ef14 ef10
  subsumption ef16 ef12

/-- Equation 2847 `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x` holds of the right division of any magma satisfying
equation 1276 `x = y ◇ (((x ◇ x) ◇ x) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux1276_2847R [Finite G] [Magma G] (h : Equation1276 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dr (dr (dr x (dr x x)) x) x := by
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ (a ◇ b)) ◇ (b ◇ (a ◇ b))) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ (z ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : (((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ ((b ◇ z) ◇ (b ◇ z)) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef13 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : x ≠ dr (dr (dr x (dr x x)) x) x := mod_symm nh
  have ef32 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0) = dr X0 X1 := by
    first | exact superpose ef13 ef15 | exact superpose ef15 ef13
  have ef220 (X0 X1 : G) : (X0 ◇ X0) ◇ X0 = dr X1 (dr X0 X1) := by
    first | exact superpose ef14 ef32 | exact superpose ef32 ef14
  have ef541 : x ≠ dr (dr ((x ◇ x) ◇ x) x) x := by
    first | exact superpose ef220 ef18 | exact superpose ef18 ef220
  have ef542 : x ≠ dr (x ◇ x) x := by
    first | exact superpose ef15 ef541 | exact superpose ef541 ef15
  subsumption ef542 ef15

theorem Equation2847_termStructuralFromFin_Equation1276_finiteDivision :
    Law2847.TermStructuralFromFin Law1276 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1276R G _ M (Law1276.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1276L G _ M (Law1276.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law2847.models_iff]
    exact fun x ↦
      @aux1276_2847R G _ M (Law1276.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 2909 `x = ((y ◇ (x ◇ y)) ◇ x) ◇ x` holds of the right division of any magma satisfying
equation 1276 `x = y ◇ (((x ◇ x) ◇ x) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux1276_2909R [Finite G] [Magma G] (h : Equation1276 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dr (dr (dr y (dr x y)) x) x := by
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ (a ◇ b)) ◇ (b ◇ (a ◇ b))) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ (z ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : (((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ ((b ◇ z) ◇ (b ◇ z)) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef13 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : x ≠ dr (dr (dr y (dr x y)) x) x := mod_symm nh
  have ef32 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0) = dr X0 X1 := by
    first | exact superpose ef13 ef15 | exact superpose ef15 ef13
  have ef220 (X0 X1 : G) : (X0 ◇ X0) ◇ X0 = dr X1 (dr X0 X1) := by
    first | exact superpose ef14 ef32 | exact superpose ef32 ef14
  have ef541 : x ≠ dr (dr ((x ◇ x) ◇ x) x) x := by
    first | exact superpose ef220 ef18 | exact superpose ef18 ef220
  have ef542 : x ≠ dr (x ◇ x) x := by
    first | exact superpose ef15 ef541 | exact superpose ef541 ef15
  subsumption ef542 ef15

theorem Equation2909_termStructuralFromFin_Equation1276_finiteDivision :
    Law2909.TermStructuralFromFin Law1276 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1276R G _ M (Law1276.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1276L G _ M (Law1276.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law2909.models_iff]
    exact fun x y ↦
      @aux1276_2909R G _ M (Law1276.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` holds of the right division of any magma satisfying
equation 1276 `x = y ◇ (((x ◇ x) ◇ x) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux1276_4273R [Finite G] [Magma G] (h : Equation1276 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x (dr x x) = dr y (dr x y) := by
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ (a ◇ b)) ◇ (b ◇ (a ◇ b))) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ (z ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : (((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ ((b ◇ z) ◇ (b ◇ z)) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef13 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x (dr x x) ≠ dr y (dr x y) := mod_symm nh
  have ef32 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0) = dr X0 X1 := by
    first | exact superpose ef13 ef15 | exact superpose ef15 ef13
  have ef220 (X0 X1 : G) : (X0 ◇ X0) ◇ X0 = dr X1 (dr X0 X1) := by
    first | exact superpose ef14 ef32 | exact superpose ef32 ef14
  have ef541 : dr x (dr x x) ≠ (x ◇ x) ◇ x := by
    first | exact superpose ef220 ef18 | exact superpose ef18 ef220
  subsumption ef541 ef220

theorem Equation4273_termStructuralFromFin_Equation1276_finiteDivision :
    Law4273.TermStructuralFromFin Law1276 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1276R G _ M (Law1276.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1276L G _ M (Law1276.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4273.models_iff]
    exact fun x y ↦
      @aux1276_4273R G _ M (Law1276.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 1492
`x = (y ◇ x) ◇ (y ◇ (y ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1492R [Finite G] [Magma G] (h : Equation1492 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : b ◇ (a ◇ (b ◇ (b ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ z ◇ (b ◇ (b ◇ b))) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := mod_symm (hrot0 ..)
  have ef9 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 : t = (p ◇ t) ◇ (q ◇ (q ◇ q)) := by
    first | exact superpose ef9 ef7 | exact superpose ef7 ef9
  have ef12 (X0 X1 : G) : X1 ◇ (X1 ◇ X1) = X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    first | exact superpose ef7 ef7
  have ef16 : q ◇ (q ◇ q) = t ◇ ((p ◇ t) ◇ ((p ◇ t) ◇ (p ◇ t))) := by
    first | exact superpose ef11 ef7 | exact superpose ef7 ef11
  have ef17 : q ◇ (q ◇ q) = p ◇ (p ◇ p) := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  have ef30 (X0 : G) : q ◇ (X0 ◇ (p ◇ (p ◇ p))) = X0 := by
    first | exact superpose ef17 ef8 | exact superpose ef8 ef17
  have ef76 (X0 : G) : q ◇ X0 = p ◇ X0 := by
    first | exact superpose ef7 ef30 | exact superpose ef30 ef7
  have ef117 : q = q ◇ (p ◇ (p ◇ (p ◇ p))) := by
    first | exact superpose ef76 ef30 | exact superpose ef30 ef76
  have ef118 : p = q := by
    first | exact superpose ef30 ef117 | exact superpose ef117 ef30
  subsumption ef118 ef10

/-- Left translation by `t` is injective in every finite magma satisfying equation 1492
`x = (y ◇ x) ◇ (y ◇ (y ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1492L [Finite G] [Magma G] (h : Equation1492 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 : q = (t ◇ p) ◇ (t ◇ (t ◇ t)) := by
    first | exact superpose ef9 ef7 | exact superpose ef7 ef9
  have ef14 : p = q := by
    first | exact superpose ef7 ef11 | exact superpose ef11 ef7
  subsumption ef14 ef10

/-- Equation 417 `x = x ◇ (x ◇ (y ◇ (x ◇ y)))` holds of the left division of any magma satisfying
equation 1492 `x = (y ◇ x) ◇ (y ◇ (y ◇ y))` and equipped with two-sided divisions. -/
private theorem aux1492_417L [Finite G] [Magma G] (h : Equation1492 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl x (dl y (dl x y))) := by
  by_contra nh
  have ef10 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl x (dl y (dl x y))) := mod_symm nh
  have ef20 (X0 X1 : G) : X0 ◇ (X1 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef45 (X0 X1 : G) : X0 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef96 : x ≠ dl x (dl x (x ◇ (x ◇ x))) := by
    first | exact superpose ef45 ef16 | exact superpose ef16 ef45
  have ef97 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef15 ef96 | exact superpose ef96 ef15
  subsumption ef97 ef15

theorem Equation417_termStructuralFromFin_Equation1492_finiteDivision :
    Law417.TermStructuralFromFin Law1492 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1492R G _ M (Law1492.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1492L G _ M (Law1492.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law417.models_iff]
    exact fun x y ↦
      @aux1492_417L G _ M (Law1492.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` holds of the left division of any magma satisfying
equation 1492 `x = (y ◇ x) ◇ (y ◇ (y ◇ y))` and equipped with two-sided divisions. -/
private theorem aux1492_4273L [Finite G] [Magma G] (h : Equation1492 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dl x (dl x x) = dl y (dl x y) := by
  by_contra nh
  have ef10 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dl x (dl x x) ≠ dl y (dl x y) := mod_symm nh
  have ef20 (X0 X1 : G) : X0 ◇ (X1 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef45 (X0 X1 : G) : X0 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef96 : dl x (dl x x) ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef45 ef16 | exact superpose ef16 ef45
  subsumption ef96 ef45

theorem Equation4273_termStructuralFromFin_Equation1492_finiteDivision :
    Law4273.TermStructuralFromFin Law1492 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1492R G _ M (Law1492.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1492L G _ M (Law1492.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4273.models_iff]
    exact fun x y ↦
      @aux1492_4273L G _ M (Law1492.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 3112 `x = (((y ◇ x) ◇ y) ◇ x) ◇ x` holds of the right division of any magma satisfying
equation 1492 `x = (y ◇ x) ◇ (y ◇ (y ◇ y))` and equipped with two-sided divisions. -/
private theorem aux1492_3112R [Finite G] [Magma G] (h : Equation1492 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dr (dr (dr (dr y x) y) x) x := by
  by_contra nh
  have ef10 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dr (dr (dr (dr y x) y) x) x := mod_symm nh
  have ef17 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef14 ef13 | exact superpose ef13 ef14
  have ef18 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef12 ef15 | exact superpose ef15 ef12
  have ef20 (X0 X1 : G) : X0 ◇ (X1 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef21 (X0 X1 : G) : X1 ◇ (X1 ◇ X1) = X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    first | exact superpose ef10 ef10
  have ef23 (X0 X1 : G) : X1 ◇ (X1 ◇ X1) = dl (X1 ◇ X0) X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef24 (X0 X1 : G) : X1 ◇ X0 = dr X0 (X1 ◇ (X1 ◇ X1)) := by
    first | exact superpose ef10 ef13 | exact superpose ef13 ef10
  have ef62 (X0 X1 X2 : G) : dl X0 X2 = X2 ◇ (dl (X0 ◇ X1) X1) := by
    first | exact superpose ef23 ef20 | exact superpose ef20 ef23
  have ef73 (X0 X1 X2 : G) : X0 ◇ X2 = dr X2 (dl (X0 ◇ X1) X1) := by
    first | exact superpose ef23 ef24 | exact superpose ef24 ef23
  have ef98 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ X0)) = (dr X0 X1) ◇ ((dr X0 X1) ◇ (dr X0 X1)) := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef130 (X0 X1 : G) : dl X0 X1 = (dr X0 X1) ◇ ((dr X0 X1) ◇ (dr X0 X1)) := by
    first | exact superpose ef20 ef98 | exact superpose ef98 ef20
  have ef211 (X0 X1 X2 : G) : dl (dr X0 X1) X2 = X2 ◇ (dl X0 X1) := by
    first | exact superpose ef12 ef62 | exact superpose ef62 ef12
  have ef474 (X0 X1 X2 : G) : (dr X0 X1) ◇ X2 = dr X2 (dl X0 X1) := by
    first | exact superpose ef12 ef73 | exact superpose ef73 ef12
  have ef2116 (X0 X1 X2 : G) : dr X1 X2 = dr X0 (X0 ◇ (dl X1 X2)) := by
    first | exact superpose ef211 ef17 | exact superpose ef17 ef211
  have ef2989 (X0 X1 X2 : G) : dr X2 X0 = (dr X1 (X1 ◇ X0)) ◇ X2 := by
    first | exact superpose ef15 ef474 | exact superpose ef474 ef15
  have ef5092 (X0 X1 X2 : G) : dr (dr X1 X0) X1 = dr X2 (X2 ◇ X0) := by
    first | exact superpose ef18 ef2116 | exact superpose ef2116 ef18
  have ef8393 (X0 X1 : G) : dl X0 (X0 ◇ X1) = (dr X0 (X0 ◇ X1)) ◇ (dr (dr X0 (X0 ◇ X1)) X1) := by
    first | exact superpose ef2989 ef130 | exact superpose ef130 ef2989
  have ef8404 (X0 X1 : G) : dl X0 (X0 ◇ X1) = dr (dr (dr X0 (X0 ◇ X1)) X1) X1 := by
    first | exact superpose ef2989 ef8393 | exact superpose ef8393 ef2989
  have ef8544 (X0 X1 : G) : dr (dr (dr X0 (X0 ◇ X1)) X1) X1 = X1 := by
    first | exact superpose ef15 ef8404 | exact superpose ef8404 ef15
  have ef11102 (X0 : G) : x ≠ dr (dr (dr X0 (X0 ◇ x)) x) x := by
    first | exact superpose ef5092 ef16 | exact superpose ef16 ef5092
  subsumption ef11102 ef8544

theorem Equation3112_termStructuralFromFin_Equation1492_finiteDivision :
    Law3112.TermStructuralFromFin Law1492 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1492R G _ M (Law1492.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1492L G _ M (Law1492.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3112.models_iff]
    exact fun x y ↦
      @aux1492_3112R G _ M (Law1492.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4588 `(x ◇ x) ◇ x = (y ◇ x) ◇ y` holds of the right division of any magma satisfying
equation 1492 `x = (y ◇ x) ◇ (y ◇ (y ◇ y))` and equipped with two-sided divisions. -/
private theorem aux1492_4588R [Finite G] [Magma G] (h : Equation1492 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr (dr x x) x = dr (dr y x) y := by
  by_contra nh
  have ef10 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dr (dr x x) x ≠ dr (dr y x) y := mod_symm nh
  have ef17 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef14 ef13 | exact superpose ef13 ef14
  have ef18 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef12 ef15 | exact superpose ef15 ef12
  have ef20 (X0 X1 : G) : X0 ◇ (X1 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef23 (X0 X1 : G) : X1 ◇ (X1 ◇ X1) = dl (X1 ◇ X0) X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef62 (X0 X1 X2 : G) : dl X0 X2 = X2 ◇ (dl (X0 ◇ X1) X1) := by
    first | exact superpose ef23 ef20 | exact superpose ef20 ef23
  have ef211 (X0 X1 X2 : G) : dl (dr X0 X1) X2 = X2 ◇ (dl X0 X1) := by
    first | exact superpose ef12 ef62 | exact superpose ef62 ef12
  have ef2116 (X0 X1 X2 : G) : dr X1 X2 = dr X0 (X0 ◇ (dl X1 X2)) := by
    first | exact superpose ef211 ef17 | exact superpose ef17 ef211
  have ef5092 (X0 X1 X2 : G) : dr (dr X1 X0) X1 = dr X2 (X2 ◇ X0) := by
    first | exact superpose ef18 ef2116 | exact superpose ef2116 ef18
  have ef11102 (X0 : G) : dr (dr x x) x ≠ dr X0 (X0 ◇ x) := by
    first | exact superpose ef5092 ef16 | exact superpose ef16 ef5092
  subsumption ef11102 ef5092

theorem Equation4588_termStructuralFromFin_Equation1492_finiteDivision :
    Law4588.TermStructuralFromFin Law1492 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1492R G _ M (Law1492.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1492L G _ M (Law1492.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4588.models_iff]
    exact fun x y ↦
      @aux1492_4588R G _ M (Law1492.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 1496
`x = (y ◇ x) ◇ (y ◇ (z ◇ z))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1496R [Finite G] [Magma G] (h : Equation1496 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b c : G) : b ◇ (a ◇ (b ◇ (c ◇ c))) = a :=
    rot_of_finite (f := fun z ↦ z ◇ (b ◇ (c ◇ c))) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b c).symm) a
  have ef7 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (hrot0 ..)
  have ef9 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef16 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0) = X2 := by
    first | exact superpose ef7 ef8 | exact superpose ef8 ef7
  have ef74 (X0 : G) : q = ((X0 ◇ X0) ◇ t) ◇ (p ◇ t) := by
    first | exact superpose ef9 ef16 | exact superpose ef16 ef9
  have ef98 : p = q := by
    first | exact superpose ef16 ef74 | exact superpose ef74 ef16
  subsumption ef98 ef10

/-- Left translation by `t` is injective in every finite magma satisfying equation 1496
`x = (y ◇ x) ◇ (y ◇ (z ◇ z))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1496L [Finite G] [Magma G] (h : Equation1496 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have ef7 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 (X0 : G) : q = (t ◇ p) ◇ (t ◇ (X0 ◇ X0)) := by
    first | exact superpose ef9 ef7 | exact superpose ef7 ef9
  have ef15 : p = q := by
    first | exact superpose ef7 ef11 | exact superpose ef11 ef7
  subsumption ef15 ef10

/-- Equation 417 `x = x ◇ (x ◇ (y ◇ (x ◇ y)))` holds of the left division of any magma satisfying
equation 1496 `x = (y ◇ x) ◇ (y ◇ (z ◇ z))` and equipped with two-sided divisions. -/
private theorem aux1496_417L [Finite G] [Magma G] (h : Equation1496 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl x (dl y (dl x y))) := by
  by_contra nh
  have hrot0 (a b c : G) : b ◇ (a ◇ (b ◇ (c ◇ c))) = a :=
    rot_of_finite (f := fun z ↦ z ◇ (b ◇ (c ◇ c))) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b c).symm) a
  have ef10 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl x (dl y (dl x y))) := mod_symm nh
  have ef20 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (X2 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef35 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef11 ef11
  have ef62 (X0 X1 : G) : dl X1 (X0 ◇ X0) = X1 := by
    first | exact superpose ef35 ef15 | exact superpose ef15 ef35
  have ef106 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X2) = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef1682 (X0 : G) : x ≠ dl x (dl x (x ◇ (X0 ◇ X0))) := by
    first | exact superpose ef106 ef16 | exact superpose ef16 ef106
  have ef1683 (X0 : G) : x ≠ dl x (X0 ◇ X0) := by
    first | exact superpose ef15 ef1682 | exact superpose ef1682 ef15
  subsumption ef1683 ef62

theorem Equation417_termStructuralFromFin_Equation1496_finiteDivision :
    Law417.TermStructuralFromFin Law1496 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1496R G _ M (Law1496.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1496L G _ M (Law1496.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law417.models_iff]
    exact fun x y ↦
      @aux1496_417L G _ M (Law1496.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 429 `x = x ◇ (y ◇ (x ◇ (y ◇ x)))` holds of the left division of any magma satisfying
equation 1496 `x = (y ◇ x) ◇ (y ◇ (z ◇ z))` and equipped with two-sided divisions. -/
private theorem aux1496_429L [Finite G] [Magma G] (h : Equation1496 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl y (dl x (dl y x))) := by
  by_contra nh
  have hrot0 (a b c : G) : b ◇ (a ◇ (b ◇ (c ◇ c))) = a :=
    rot_of_finite (f := fun z ↦ z ◇ (b ◇ (c ◇ c))) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b c).symm) a
  have ef10 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl y (dl x (dl y x))) := mod_symm nh
  have ef20 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (X2 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef35 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef11 ef11
  have ef62 (X0 X1 : G) : dl X1 (X0 ◇ X0) = X1 := by
    first | exact superpose ef35 ef15 | exact superpose ef15 ef35
  have ef106 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X2) = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef1682 (X0 : G) : x ≠ dl x (dl y (y ◇ (X0 ◇ X0))) := by
    first | exact superpose ef106 ef16 | exact superpose ef16 ef106
  have ef1683 (X0 : G) : x ≠ dl x (X0 ◇ X0) := by
    first | exact superpose ef15 ef1682 | exact superpose ef1682 ef15
  subsumption ef1683 ef62

theorem Equation429_termStructuralFromFin_Equation1496_finiteDivision :
    Law429.TermStructuralFromFin Law1496 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1496R G _ M (Law1496.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1496L G _ M (Law1496.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law429.models_iff]
    exact fun x y ↦
      @aux1496_429L G _ M (Law1496.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 440 `x = x ◇ (y ◇ (y ◇ (y ◇ y)))` holds of the left division of any magma satisfying
equation 1496 `x = (y ◇ x) ◇ (y ◇ (z ◇ z))` and equipped with two-sided divisions. -/
private theorem aux1496_440L [Finite G] [Magma G] (h : Equation1496 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl y (dl y (dl y y))) := by
  by_contra nh
  have hrot0 (a b c : G) : b ◇ (a ◇ (b ◇ (c ◇ c))) = a :=
    rot_of_finite (f := fun z ↦ z ◇ (b ◇ (c ◇ c))) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b c).symm) a
  have ef10 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl y (dl y (dl y y))) := mod_symm nh
  have ef20 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (X2 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef35 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef11 ef11
  have ef62 (X0 X1 : G) : dl X1 (X0 ◇ X0) = X1 := by
    first | exact superpose ef35 ef15 | exact superpose ef15 ef35
  have ef106 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X2) = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef1682 (X0 : G) : x ≠ dl x (dl y (y ◇ (X0 ◇ X0))) := by
    first | exact superpose ef106 ef16 | exact superpose ef16 ef106
  have ef1683 (X0 : G) : x ≠ dl x (X0 ◇ X0) := by
    first | exact superpose ef15 ef1682 | exact superpose ef1682 ef15
  subsumption ef1683 ef62

theorem Equation440_termStructuralFromFin_Equation1496_finiteDivision :
    Law440.TermStructuralFromFin Law1496 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1496R G _ M (Law1496.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1496L G _ M (Law1496.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law440.models_iff]
    exact fun x y ↦
      @aux1496_440L G _ M (Law1496.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 452 `x = x ◇ (y ◇ (z ◇ (y ◇ z)))` holds of the left division of any magma satisfying
equation 1496 `x = (y ◇ x) ◇ (y ◇ (z ◇ z))` and equipped with two-sided divisions. -/
private theorem aux1496_452L [Finite G] [Magma G] (h : Equation1496 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    x = dl x (dl y (dl z (dl y z))) := by
  by_contra nh
  have hrot0 (a b c : G) : b ◇ (a ◇ (b ◇ (c ◇ c))) = a :=
    rot_of_finite (f := fun z ↦ z ◇ (b ◇ (c ◇ c))) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b c).symm) a
  have ef10 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : x ≠ dl x (dl y (dl z (dl y z))) := mod_symm nh
  have ef20 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (X2 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef35 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef11 ef11
  have ef62 (X0 X1 : G) : dl X1 (X0 ◇ X0) = X1 := by
    first | exact superpose ef35 ef15 | exact superpose ef15 ef35
  have ef106 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X2) = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef1682 (X0 : G) : x ≠ dl x (dl y (y ◇ (X0 ◇ X0))) := by
    first | exact superpose ef106 ef16 | exact superpose ef16 ef106
  have ef1683 (X0 : G) : x ≠ dl x (X0 ◇ X0) := by
    first | exact superpose ef15 ef1682 | exact superpose ef1682 ef15
  subsumption ef1683 ef62

theorem Equation452_termStructuralFromFin_Equation1496_finiteDivision :
    Law452.TermStructuralFromFin Law1496 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1496R G _ M (Law1496.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1496L G _ M (Law1496.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law452.models_iff]
    exact fun x y z ↦
      @aux1496_452L G _ M (Law1496.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` holds of the left division of any magma satisfying
equation 1496 `x = (y ◇ x) ◇ (y ◇ (z ◇ z))` and equipped with two-sided divisions. -/
private theorem aux1496_4273L [Finite G] [Magma G] (h : Equation1496 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dl x (dl x x) = dl y (dl x y) := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dl x (dl x x) ≠ dl y (dl x y) := mod_symm nh
  have ef20 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ (X2 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef106 (X0 X1 X2 : G) : X0 ◇ (X2 ◇ X2) = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef1682 (X0 : G) : dl x (dl x x) ≠ x ◇ (X0 ◇ X0) := by
    first | exact superpose ef106 ef16 | exact superpose ef16 ef106
  subsumption ef1682 ef106

theorem Equation4273_termStructuralFromFin_Equation1496_finiteDivision :
    Law4273.TermStructuralFromFin Law1496 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1496R G _ M (Law1496.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1496L G _ M (Law1496.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4273.models_iff]
    exact fun x y ↦
      @aux1496_4273L G _ M (Law1496.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 3068 `x = (((x ◇ y) ◇ x) ◇ y) ◇ x` holds of the right division of any magma satisfying
equation 1496 `x = (y ◇ x) ◇ (y ◇ (z ◇ z))` and equipped with two-sided divisions. -/
private theorem aux1496_3068R [Finite G] [Magma G] (h : Equation1496 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dr (dr (dr (dr x y) x) y) x := by
  by_contra nh
  have hrot0 (a b c : G) : b ◇ (a ◇ (b ◇ (c ◇ c))) = a :=
    rot_of_finite (f := fun z ↦ z ◇ (b ◇ (c ◇ c))) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b c).symm) a
  have ef10 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (hrot0 ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 : x ≠ dr (dr (dr (dr x y) x) y) x := mod_symm nh
  have ef23 (X0 X1 X2 : G) : ((dr X0 (X1 ◇ X1)) ◇ X2) ◇ X0 = X2 := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef35 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef11 ef11
  have ef63 (X0 X1 : G) : dr (X0 ◇ X0) X1 = X1 := by
    first | exact superpose ef35 ef13 | exact superpose ef13 ef35
  have ef144 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 (X2 ◇ X2)) ◇ X0 := by
    first | exact superpose ef23 ef13 | exact superpose ef13 ef23
  have ef2018 (X0 X1 X2 : G) : dr (dr (dr X0 (X1 ◇ X1)) X0) X2 = X2 := by
    first | exact superpose ef144 ef63 | exact superpose ef63 ef144
  have ef2035 (X0 X1 X2 : G) : dr X1 (X2 ◇ X2) = dr (dr X0 X1) X0 := by
    first | exact superpose ef144 ef13 | exact superpose ef13 ef144
  have ef21538 (X0 : G) : x ≠ dr (dr (dr y (X0 ◇ X0)) y) x := by
    first | exact superpose ef2035 ef16 | exact superpose ef16 ef2035
  subsumption ef21538 ef2018

theorem Equation3068_termStructuralFromFin_Equation1496_finiteDivision :
    Law3068.TermStructuralFromFin Law1496 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1496R G _ M (Law1496.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1496L G _ M (Law1496.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3068.models_iff]
    exact fun x y ↦
      @aux1496_3068R G _ M (Law1496.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 3112 `x = (((y ◇ x) ◇ y) ◇ x) ◇ x` holds of the right division of any magma satisfying
equation 1496 `x = (y ◇ x) ◇ (y ◇ (z ◇ z))` and equipped with two-sided divisions. -/
private theorem aux1496_3112R [Finite G] [Magma G] (h : Equation1496 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dr (dr (dr (dr y x) y) x) x := by
  by_contra nh
  have hrot0 (a b c : G) : b ◇ (a ◇ (b ◇ (c ◇ c))) = a :=
    rot_of_finite (f := fun z ↦ z ◇ (b ◇ (c ◇ c))) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b c).symm) a
  have ef10 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (hrot0 ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 : x ≠ dr (dr (dr (dr y x) y) x) x := mod_symm nh
  have ef23 (X0 X1 X2 : G) : ((dr X0 (X1 ◇ X1)) ◇ X2) ◇ X0 = X2 := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef35 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef11 ef11
  have ef63 (X0 X1 : G) : dr (X0 ◇ X0) X1 = X1 := by
    first | exact superpose ef35 ef13 | exact superpose ef13 ef35
  have ef144 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 (X2 ◇ X2)) ◇ X0 := by
    first | exact superpose ef23 ef13 | exact superpose ef13 ef23
  have ef2018 (X0 X1 X2 : G) : dr (dr (dr X0 (X1 ◇ X1)) X0) X2 = X2 := by
    first | exact superpose ef144 ef63 | exact superpose ef63 ef144
  have ef2035 (X0 X1 X2 : G) : dr X1 (X2 ◇ X2) = dr (dr X0 X1) X0 := by
    first | exact superpose ef144 ef13 | exact superpose ef13 ef144
  have ef21538 (X0 : G) : x ≠ dr (dr (dr x (X0 ◇ X0)) x) x := by
    first | exact superpose ef2035 ef16 | exact superpose ef16 ef2035
  subsumption ef21538 ef2018

theorem Equation3112_termStructuralFromFin_Equation1496_finiteDivision :
    Law3112.TermStructuralFromFin Law1496 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1496R G _ M (Law1496.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1496L G _ M (Law1496.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3112.models_iff]
    exact fun x y ↦
      @aux1496_3112R G _ M (Law1496.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 3152 `x = (((y ◇ y) ◇ y) ◇ y) ◇ x` holds of the right division of any magma satisfying
equation 1496 `x = (y ◇ x) ◇ (y ◇ (z ◇ z))` and equipped with two-sided divisions. -/
private theorem aux1496_3152R [Finite G] [Magma G] (h : Equation1496 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dr (dr (dr (dr y y) y) y) x := by
  by_contra nh
  have hrot0 (a b c : G) : b ◇ (a ◇ (b ◇ (c ◇ c))) = a :=
    rot_of_finite (f := fun z ↦ z ◇ (b ◇ (c ◇ c))) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b c).symm) a
  have ef10 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (hrot0 ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 : x ≠ dr (dr (dr (dr y y) y) y) x := mod_symm nh
  have ef23 (X0 X1 X2 : G) : ((dr X0 (X1 ◇ X1)) ◇ X2) ◇ X0 = X2 := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef35 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef11 ef11
  have ef63 (X0 X1 : G) : dr (X0 ◇ X0) X1 = X1 := by
    first | exact superpose ef35 ef13 | exact superpose ef13 ef35
  have ef144 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 (X2 ◇ X2)) ◇ X0 := by
    first | exact superpose ef23 ef13 | exact superpose ef13 ef23
  have ef2018 (X0 X1 X2 : G) : dr (dr (dr X0 (X1 ◇ X1)) X0) X2 = X2 := by
    first | exact superpose ef144 ef63 | exact superpose ef63 ef144
  have ef2035 (X0 X1 X2 : G) : dr X1 (X2 ◇ X2) = dr (dr X0 X1) X0 := by
    first | exact superpose ef144 ef13 | exact superpose ef13 ef144
  have ef21559 (X0 : G) : x ≠ dr (dr (dr y (X0 ◇ X0)) y) x := by
    first | exact superpose ef2035 ef16 | exact superpose ef16 ef2035
  subsumption ef21559 ef2018

theorem Equation3152_termStructuralFromFin_Equation1496_finiteDivision :
    Law3152.TermStructuralFromFin Law1496 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1496R G _ M (Law1496.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1496L G _ M (Law1496.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3152.models_iff]
    exact fun x y ↦
      @aux1496_3152R G _ M (Law1496.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 3201 `x = (((y ◇ z) ◇ y) ◇ z) ◇ x` holds of the right division of any magma satisfying
equation 1496 `x = (y ◇ x) ◇ (y ◇ (z ◇ z))` and equipped with two-sided divisions. -/
private theorem aux1496_3201R [Finite G] [Magma G] (h : Equation1496 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    x = dr (dr (dr (dr y z) y) z) x := by
  by_contra nh
  have hrot0 (a b c : G) : b ◇ (a ◇ (b ◇ (c ◇ c))) = a :=
    rot_of_finite (f := fun z ↦ z ◇ (b ◇ (c ◇ c))) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b c).symm) a
  have ef10 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := mod_symm (hrot0 ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 : x ≠ dr (dr (dr (dr y z) y) z) x := mod_symm nh
  have ef23 (X0 X1 X2 : G) : ((dr X0 (X1 ◇ X1)) ◇ X2) ◇ X0 = X2 := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef35 (X0 X1 : G) : X0 ◇ X0 = X1 ◇ X1 := by
    first | exact superpose ef11 ef11
  have ef63 (X0 X1 : G) : dr (X0 ◇ X0) X1 = X1 := by
    first | exact superpose ef35 ef13 | exact superpose ef13 ef35
  have ef144 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 (X2 ◇ X2)) ◇ X0 := by
    first | exact superpose ef23 ef13 | exact superpose ef13 ef23
  have ef2018 (X0 X1 X2 : G) : dr (dr (dr X0 (X1 ◇ X1)) X0) X2 = X2 := by
    first | exact superpose ef144 ef63 | exact superpose ef63 ef144
  have ef2035 (X0 X1 X2 : G) : dr X1 (X2 ◇ X2) = dr (dr X0 X1) X0 := by
    first | exact superpose ef144 ef13 | exact superpose ef13 ef144
  have ef21538 (X0 : G) : x ≠ dr (dr (dr z (X0 ◇ X0)) z) x := by
    first | exact superpose ef2035 ef16 | exact superpose ef16 ef2035
  subsumption ef21538 ef2018

theorem Equation3201_termStructuralFromFin_Equation1496_finiteDivision :
    Law3201.TermStructuralFromFin Law1496 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1496R G _ M (Law1496.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1496L G _ M (Law1496.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law3201.models_iff]
    exact fun x y z ↦
      @aux1496_3201R G _ M (Law1496.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Equation 4588 `(x ◇ x) ◇ x = (y ◇ x) ◇ y` holds of the right division of any magma satisfying
equation 1496 `x = (y ◇ x) ◇ (y ◇ (z ◇ z))` and equipped with two-sided divisions. -/
private theorem aux1496_4588R [Finite G] [Magma G] (h : Equation1496 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr (dr x x) x = dr (dr y x) y := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 : dr (dr x x) x ≠ dr (dr y x) y := mod_symm nh
  have ef23 (X0 X1 X2 : G) : ((dr X0 (X1 ◇ X1)) ◇ X2) ◇ X0 = X2 := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef144 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 (X2 ◇ X2)) ◇ X0 := by
    first | exact superpose ef23 ef13 | exact superpose ef13 ef23
  have ef2035 (X0 X1 X2 : G) : dr X1 (X2 ◇ X2) = dr (dr X0 X1) X0 := by
    first | exact superpose ef144 ef13 | exact superpose ef13 ef144
  have ef21534 (X0 : G) : dr (dr x x) x ≠ dr x (X0 ◇ X0) := by
    first | exact superpose ef2035 ef16 | exact superpose ef16 ef2035
  subsumption ef21534 ef2035

theorem Equation4588_termStructuralFromFin_Equation1496_finiteDivision :
    Law4588.TermStructuralFromFin Law1496 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1496R G _ M (Law1496.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1496L G _ M (Law1496.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4588.models_iff]
    exact fun x y ↦
      @aux1496_4588R G _ M (Law1496.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

end Law.MagmaLaw
