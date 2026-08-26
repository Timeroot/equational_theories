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

theorem Equation53_termStructuralFromFin_Equation66_finiteDivisionL :
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

theorem Equation2494_termStructuralFromFin_Equation66_finiteDivisionR :
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

theorem Equation221_termStructuralFromFin_Equation115_finiteDivisionR :
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

theorem Equation4273_termStructuralFromFin_Equation115_finiteDivisionR :
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

/-- Left translation by `t` is injective in every finite magma satisfying equation 124
`x = y ◇ ((y ◇ x) ◇ x)`. Its models are therefore quasigroups, and the division is the inverse
translation -- a term, at an exponent the carrier fixes. -/
private theorem inj124L [Finite G] [Magma G] (h : Equation124 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ (b ◇ a) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ (b ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef13 : q = (t ◇ (t ◇ p)) ◇ (t ◇ p) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef16 : p = q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef16 ef10

/-- Equation 3343 `x ◇ y = y ◇ (x ◇ (x ◇ y))` holds of the left division of any magma satisfying
equation 124 `x = y ◇ ((y ◇ x) ◇ x)` and equipped with that one division. -/
private theorem aux124_3343L1 [Finite G] [Magma G] (h : Equation124 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dl x y = dl y (dl x (dl x y)) := by
  by_contra nh
  have ef8 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have ef10 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef11 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef12 : dl x y ≠ dl y (dl x (dl x y)) := mod_symm nh
  have ef15 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = dl X1 X0 := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  have ef17 (X0 X1 : G) : X0 ◇ (dl X1 X0) = dl X1 (dl X1 X0) := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef165 : dl x y ≠ dl y (y ◇ (dl x y)) := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  subsumption ef165 ef11

theorem Equation3343_termStructuralFromFin_Equation124_finiteDivisionL :
    Law3343.TermStructuralFromFin Law124 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj124L G _ M (Law124.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law3343.models_iff]
    exact fun x y ↦
      @aux124_3343L1 G _ M (Law124.models_iff.mp hGL) dl h1 h2 x y

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

theorem Equation63_termStructuralFromFin_Equation125_finiteDivisionL :
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

theorem Equation1692_termStructuralFromFin_Equation125_finiteDivisionL :
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

theorem Equation3954_termStructuralFromFin_Equation125_finiteDivisionR :
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

theorem Equation511_termStructuralFromFin_Equation464_finiteDivisionL :
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

theorem Equation614_termStructuralFromFin_Equation464_finiteDivisionL :
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

theorem Equation714_termStructuralFromFin_Equation464_finiteDivisionL :
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

theorem Equation1223_termStructuralFromFin_Equation464_finiteDivisionL :
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

theorem Equation2238_termStructuralFromFin_Equation464_finiteDivisionL :
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

theorem Equation2338_termStructuralFromFin_Equation464_finiteDivisionL :
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

theorem Equation2847_termStructuralFromFin_Equation464_finiteDivisionL :
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

theorem Equation4380_termStructuralFromFin_Equation464_finiteDivisionL :
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

theorem Equation4435_termStructuralFromFin_Equation464_finiteDivisionL :
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

theorem Equation437_termStructuralFromFin_Equation467_finiteDivisionL :
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

/-- Left translation by `t` is injective in every finite magma satisfying equation 473
`x = y ◇ (x ◇ (y ◇ (x ◇ x)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj473L [Finite G] [Magma G] (h : Equation473 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (b ◇ ((b ◇ a) ◇ (b ◇ a))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (b ◇ (z ◇ z)))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 : q = (t ◇ p) ◇ (t ◇ ((t ◇ p) ◇ (t ◇ p))) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef13 : p = q := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  subsumption ef13 ef10

/-- Equation 429 `x = x ◇ (y ◇ (x ◇ (y ◇ x)))` holds of the left division of any magma satisfying
equation 473 `x = y ◇ (x ◇ (y ◇ (x ◇ x)))` and equipped with that one division. -/
private theorem aux473_429L1 [Finite G] [Magma G] (h : Equation473 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl y (dl x (dl y x))) := by
  by_contra nh
  have ef8 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef12 : x ≠ dl x (dl y (dl x (dl y x))) := mod_symm nh
  have ef13 (X0 X1 : G) : X0 ◇ (X1 ◇ (X0 ◇ X0)) = dl X1 X0 := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  have ef19 (X0 X1 : G) : X0 ◇ (X1 ◇ X1) = dl X1 (dl X0 X1) := by
    first | exact superpose ef13 ef11 | exact superpose ef11 ef13
  have ef32 : x ≠ dl x (dl y (y ◇ (x ◇ x))) := by
    first | exact superpose ef19 ef12 | exact superpose ef12 ef19
  have ef34 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef11 ef32 | exact superpose ef32 ef11
  subsumption ef34 ef11

theorem Equation429_termStructuralFromFin_Equation473_finiteDivisionL :
    Law429.TermStructuralFromFin Law473 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj473L G _ M (Law473.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law429.models_iff]
    exact fun x y ↦
      @aux473_429L1 G _ M (Law473.models_iff.mp hGL) dl h1 h2 x y

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

theorem Equation417_termStructuralFromFin_Equation477_finiteDivisionL :
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

theorem Equation4273_termStructuralFromFin_Equation477_finiteDivisionL :
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

theorem Equation3112_termStructuralFromFin_Equation477_finiteDivisionR :
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

theorem Equation4588_termStructuralFromFin_Equation477_finiteDivisionR :
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

theorem Equation417_termStructuralFromFin_Equation481_finiteDivisionL :
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

theorem Equation429_termStructuralFromFin_Equation481_finiteDivisionL :
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

theorem Equation440_termStructuralFromFin_Equation481_finiteDivisionL :
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

theorem Equation452_termStructuralFromFin_Equation481_finiteDivisionL :
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

theorem Equation4273_termStructuralFromFin_Equation481_finiteDivisionL :
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

theorem Equation3068_termStructuralFromFin_Equation481_finiteDivisionR :
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

theorem Equation3112_termStructuralFromFin_Equation481_finiteDivisionR :
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

theorem Equation3152_termStructuralFromFin_Equation481_finiteDivisionR :
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

theorem Equation3201_termStructuralFromFin_Equation481_finiteDivisionR :
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

theorem Equation4588_termStructuralFromFin_Equation481_finiteDivisionR :
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

/-- Left translation by `t` is injective in every finite magma satisfying equation 504
`x = y ◇ (y ◇ (x ◇ (y ◇ y)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj504L [Finite G] [Magma G] (h : Equation504 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef9 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef13 : q = (t ◇ (t ◇ p)) ◇ (t ◇ t) := by
    first | exact superpose ef11 ef9 | exact superpose ef9 ef11
  have ef16 : p = q := by
    first | exact superpose ef9 ef13 | exact superpose ef13 ef9
  subsumption ef16 ef12

/-- Equation 427 `x = x ◇ (y ◇ (x ◇ (x ◇ y)))` holds of the left division of any magma satisfying
equation 504 `x = y ◇ (y ◇ (x ◇ (y ◇ y)))` and equipped with that one division. -/
private theorem aux504_427L1 [Finite G] [Magma G] (h : Equation504 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl y (dl x (dl x y))) := by
  by_contra nh
  have ef9 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef14 : x ≠ dl x (dl y (dl x (dl x y))) := mod_symm nh
  have ef15 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef9 ef13 | exact superpose ef13 ef9
  have ef38 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl X0 (dl X0 X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef152 : x ≠ dl x (dl y (y ◇ (x ◇ x))) := by
    first | exact superpose ef38 ef14 | exact superpose ef14 ef38
  have ef153 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef13 ef152 | exact superpose ef152 ef13
  subsumption ef153 ef13

theorem Equation427_termStructuralFromFin_Equation504_finiteDivisionL :
    Law427.TermStructuralFromFin Law504 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj504L G _ M (Law504.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law427.models_iff]
    exact fun x y ↦
      @aux504_427L1 G _ M (Law504.models_iff.mp hGL) dl h1 h2 x y

/-- Equation 1020 `x = x ◇ ((x ◇ (x ◇ x)) ◇ x)` holds of the left division of any magma satisfying
equation 504 `x = y ◇ (y ◇ (x ◇ (y ◇ y)))` and equipped with that one division. -/
private theorem aux504_1020L1 [Finite G] [Magma G] (h : Equation504 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl x (dl (dl x (dl x x)) x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef9 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef10 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef13 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef14 : x ≠ dl x (dl (dl x (dl x x)) x) := mod_symm nh
  have ef15 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef9 ef13 | exact superpose ef13 ef9
  have ef19 (X0 X1 : G) : X1 ◇ X1 = dl (X1 ◇ (X1 ◇ X0)) X0 := by
    first | exact superpose ef10 ef13 | exact superpose ef13 ef10
  have ef38 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl X0 (dl X0 X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef152 : x ≠ dl x (dl (x ◇ (x ◇ x)) x) := by
    first | exact superpose ef38 ef14 | exact superpose ef14 ef38
  have ef153 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef19 ef152 | exact superpose ef152 ef19
  subsumption ef153 ef13

theorem Equation1020_termStructuralFromFin_Equation504_finiteDivisionL :
    Law1020.TermStructuralFromFin Law504 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj504L G _ M (Law504.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law1020.models_iff]
    exact fun x ↦
      @aux504_1020L1 G _ M (Law504.models_iff.mp hGL) dl h1 h2 x

/-- Left translation by `t` is injective in every finite magma satisfying equation 543
`x = y ◇ (z ◇ (x ◇ (y ◇ z)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj543L [Finite G] [Magma G] (h : Equation543 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef9 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef16 (X0 : G) : q = (X0 ◇ (t ◇ p)) ◇ (X0 ◇ t) := by
    first | exact superpose ef11 ef9 | exact superpose ef9 ef11
  have ef24 : p = q := by
    first | exact superpose ef9 ef16 | exact superpose ef16 ef9
  subsumption ef24 ef12

/-- Right translation by `t` is injective in every finite magma satisfying equation 543
`x = y ◇ (z ◇ (x ◇ (y ◇ z)))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj543R [Finite G] [Magma G] (h : Equation543 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef11 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef13 (X0 : G) : q ◇ (t ◇ (X0 ◇ (p ◇ t))) = X0 := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef15 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X0) = X2 := by
    first | exact superpose ef8 ef8
  have ef76 (X0 : G) : q = t ◇ ((X0 ◇ (p ◇ t)) ◇ X0) := by
    first | exact superpose ef13 ef8 | exact superpose ef8 ef13
  have ef87 : p = q := by
    first | exact superpose ef15 ef76 | exact superpose ef76 ef15
  subsumption ef87 ef12

/-- Equation 43 `x ◇ y = y ◇ x` holds of the right division of any magma satisfying equation 543
`x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_43R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x y = dr y x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x y ≠ dr y x := mod_symm nh
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef157 (X0 X1 : G) : dr X0 X1 = dr X1 X0 := by
    first | exact superpose ef109 ef15 | exact superpose ef15 ef109
  have ef599 : dr x y ≠ dr x y := by
    first | exact superpose ef157 ef18 | exact superpose ef18 ef157
  exact absurd rfl ef599

theorem Equation43_termStructuralFromFin_Equation543_finiteDivisionR :
    Law43.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law43.models_iff]
    exact fun x y ↦
      @aux543_43R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4283 `x ◇ (x ◇ y) = x ◇ (y ◇ x)` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4283R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x (dr x y) = dr x (dr y x) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x (dr x y) ≠ dr x (dr y x) := mod_symm nh
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef157 (X0 X1 : G) : dr X0 X1 = dr X1 X0 := by
    first | exact superpose ef109 ef15 | exact superpose ef15 ef109
  have ef605 : dr x (dr x y) ≠ dr x (dr x y) := by
    first | exact superpose ef157 ef18 | exact superpose ef18 ef157
  exact absurd rfl ef605

theorem Equation4283_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4283.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4283.models_iff]
    exact fun x y ↦
      @aux543_4283R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4358 `x ◇ (y ◇ z) = x ◇ (z ◇ y)` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4358R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    dr x (dr y z) = dr x (dr z y) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x (dr y z) ≠ dr x (dr z y) := mod_symm nh
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef157 (X0 X1 : G) : dr X0 X1 = dr X1 X0 := by
    first | exact superpose ef109 ef15 | exact superpose ef15 ef109
  have ef605 : dr x (dr y z) ≠ dr x (dr y z) := by
    first | exact superpose ef157 ef18 | exact superpose ef18 ef157
  exact absurd rfl ef605

theorem Equation4358_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4358.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4358.models_iff]
    exact fun x y z ↦
      @aux543_4358R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

set_option maxHeartbeats 600000 in
/-- Equation 4364 `x ◇ (y ◇ z) = y ◇ (z ◇ x)` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4364R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    dr x (dr y z) = dr y (dr z x) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : c ◇ ((b ◇ a) ◇ (b ◇ c)) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ c)) (g := fun z ↦ c ◇ z)
      (fun z ↦ hrot0 z b c) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef13 (X0 X1 X2 : G) : X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (hrot1 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : dr x (dr y z) ≠ dr y (dr z x) := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef25 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X0) = X2 := by
    first | exact superpose ef11 ef11
  have ef26 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ (X1 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef32 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ X2) = dl X2 X0 := by
    first | exact superpose ef16 ef12 | exact superpose ef12 ef16
  have ef37 (X0 X1 X2 : G) : ((dr X0 X1) ◇ (X1 ◇ X2)) ◇ X0 = X2 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef59 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) = X3 := by
    first | exact superpose ef12 ef13 | exact superpose ef13 ef12
  have ef81 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 X2) ◇ (X2 ◇ X0) := by
    first | exact superpose ef14 ef21 | exact superpose ef21 ef14
  have ef86 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = (dr (X1 ◇ X2) X3) ◇ (X3 ◇ X0) := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef151 (X0 X1 : G) : X0 ◇ X1 = dl X0 X1 := by
    first | exact superpose ef19 ef109 | exact superpose ef109 ef19
  have ef159 (X0 X1 X2 : G) : dr X1 X0 = (dr X1 X2) ◇ (X2 ◇ X0) := by
    first | exact superpose ef109 ef21 | exact superpose ef21 ef109
  have ef163 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr (X1 ◇ X2) X0 := by
    first | exact superpose ef109 ef11 | exact superpose ef11 ef109
  have ef174 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3) = dr X3 X0 := by
    first | exact superpose ef21 ef24 | exact superpose ef24 ef21
  have ef175 (X0 X1 X2 : G) : dr X2 X0 = (dr X1 X0) ◇ (X1 ◇ X2) := by
    first | exact superpose ef109 ef24 | exact superpose ef24 ef109
  have ef264 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = (dr X1 X2) ◇ X0 := by
    first | exact superpose ef25 ef21 | exact superpose ef21 ef25
  have ef365 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = dl (X1 ◇ (X2 ◇ X0)) X3 := by
    first | exact superpose ef12 ef26 | exact superpose ef26 ef12
  have ef432 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ (X2 ◇ X0)) ◇ X3 := by
    first | exact superpose ef151 ef365 | exact superpose ef365 ef151
  have ef808 (X0 X1 X2 : G) : (dl X0 X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef26 ef37 | exact superpose ef37 ef26
  have ef853 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef151 ef808 | exact superpose ef808 ef151
  have ef3148 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ ((X2 ◇ X0) ◇ X3) = dr X3 (dr X0 X1) := by
    first | exact superpose ef81 ef24 | exact superpose ef24 ef81
  have ef3178 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X2) := by
    first | exact superpose ef264 ef3148 | exact superpose ef3148 ef264
  have ef3247 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X1 ◇ ((X2 ◇ X0) ◇ (dr X2 X3)) := by
    first | exact superpose ef853 ef3178 | exact superpose ef3178 ef853
  have ef3301 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X1 ◇ (X2 ◇ (dr (dr X2 X3) X0)) := by
    first | exact superpose ef853 ef3247 | exact superpose ef3247 ef853
  have ef8268 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = dl (((X1 ◇ (X2 ◇ X4)) ◇ X0) ◇ X4) X3 := by
    first | exact superpose ef59 ef32 | exact superpose ef32 ef59
  have ef8319 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = (((X1 ◇ (X2 ◇ X4)) ◇ X0) ◇ X4) ◇ X3 := by
    first | exact superpose ef151 ef8268 | exact superpose ef8268 ef151
  have ef8492 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = ((X1 ◇ (X2 ◇ X4)) ◇ X0) ◇ (dr X3 X4) := by
    first | exact superpose ef853 ef8319 | exact superpose ef8319 ef853
  have ef8650 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = (X1 ◇ (X2 ◇ X4)) ◇ (dr (dr X3 X4) X0) := by
    first | exact superpose ef853 ef8492 | exact superpose ef8492 ef853
  have ef8791 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = (X1 ◇ X2) ◇ ((dr (dr X3 X4) X0) ◇ X4) := by
    first | exact superpose ef432 ef8650 | exact superpose ef8650 ef432
  have ef8922 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ (dr ((dr (dr X3 X4) X0) ◇ X4) X2) := by
    first | exact superpose ef853 ef8791 | exact superpose ef8791 ef853
  have ef9035 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ ((dr (dr X3 X4) X0) ◇ (X4 ◇ X2)) := by
    first | exact superpose ef163 ef8922 | exact superpose ef8922 ef163
  have ef9127 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ ((dr X3 X4) ◇ ((X4 ◇ X2) ◇ X0)) := by
    first | exact superpose ef264 ef9035 | exact superpose ef9035 ef264
  have ef9207 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ (X3 ◇ (((X4 ◇ X2) ◇ X0) ◇ X4)) := by
    first | exact superpose ef264 ef9127 | exact superpose ef9127 ef264
  have ef9272 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ (X3 ◇ ((X4 ◇ X2) ◇ (dr X4 X0))) := by
    first | exact superpose ef853 ef9207 | exact superpose ef9207 ef853
  have ef9325 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ (X3 ◇ (X4 ◇ (dr (dr X4 X0) X2))) := by
    first | exact superpose ef853 ef9272 | exact superpose ef9272 ef853
  have ef9371 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ (dr X0 (dr X2 X3)) := by
    first | exact superpose ef3301 ef9325 | exact superpose ef9325 ef3301
  have ef9411 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (dr X0 X3) = X1 ◇ (dr X0 (dr X2 X3)) := by
    first | exact superpose ef853 ef9371 | exact superpose ef9371 ef853
  have ef9439 (X0 X1 X2 X3 : G) : X1 ◇ (dr (dr X0 X3) X2) = X1 ◇ (dr X0 (dr X2 X3)) := by
    first | exact superpose ef853 ef9411 | exact superpose ef9411 ef853
  have ef32492 (X0 X1 X2 X3 X4 : G) :
      (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) = (dr X0 X2) ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef159 ef86 | exact superpose ef86 ef159
  have ef32549 (X0 X1 X2 X3 X4 : G) :
      (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) = X0 ◇ (((X2 ◇ X1) ◇ X3) ◇ X2) := by
    first | exact superpose ef264 ef32492 | exact superpose ef32492 ef264
  have ef32713 (X0 X1 X2 X3 X4 : G) :
      (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) = X0 ◇ ((X2 ◇ X1) ◇ (dr X2 X3)) := by
    first | exact superpose ef853 ef32549 | exact superpose ef32549 ef853
  have ef32853 (X0 X1 X2 X3 X4 : G) :
      (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) = X0 ◇ (X2 ◇ (dr (dr X2 X3) X1)) := by
    first | exact superpose ef853 ef32713 | exact superpose ef32713 ef853
  have ef32960 (X0 X1 X3 X4 : G) : dr X3 (dr X1 X0) = (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) := by
    first | exact superpose ef3301 ef32853 | exact superpose ef32853 ef3301
  have ef33040 (X0 X1 X3 : G) : dr X3 (dr X0 X1) = dr X3 (dr X1 X0) := by
    first | exact superpose ef81 ef32960 | exact superpose ef32960 ef81
  have ef35808 (X0 X1 X2 X3 X4 : G) :
      dr X4 (dr X0 X1) = (dr X2 X3) ◇ (((X3 ◇ (X1 ◇ X2)) ◇ X0) ◇ X4) := by
    first | exact superpose ef174 ef24 | exact superpose ef24 ef174
  have ef35921 (X0 X1 X2 X3 X4 : G) :
      dr X4 (dr X0 X1) = X2 ◇ ((((X3 ◇ (X1 ◇ X2)) ◇ X0) ◇ X4) ◇ X3) := by
    first | exact superpose ef264 ef35808 | exact superpose ef35808 ef264
  have ef36187 (X0 X1 X2 X3 X4 : G) :
      dr X4 (dr X0 X1) = X2 ◇ (((X3 ◇ (X1 ◇ X2)) ◇ X0) ◇ (dr X3 X4)) := by
    first | exact superpose ef853 ef35921 | exact superpose ef35921 ef853
  have ef36442 (X0 X1 X2 X3 X4 : G) :
      dr X4 (dr X0 X1) = X2 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (dr (dr X3 X4) X0)) := by
    first | exact superpose ef853 ef36187 | exact superpose ef36187 ef853
  have ef36670 (X0 X1 X2 X3 X4 : G) :
      dr X4 (dr X0 X1) = X2 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (dr X3 (dr X0 X4))) := by
    first | exact superpose ef9439 ef36442 | exact superpose ef36442 ef9439
  have ef36882 (X0 X1 X2 X3 X4 : G) :
      dr X4 (dr X0 X1) = X2 ◇ ((X3 ◇ X1) ◇ ((dr X3 (dr X0 X4)) ◇ X2)) := by
    first | exact superpose ef432 ef36670 | exact superpose ef36670 ef432
  have ef37061 (X0 X1 X3 X4 : G) : dr X4 (dr X0 X1) = dl (dr X3 (dr X0 X4)) (X3 ◇ X1) := by
    first | exact superpose ef26 ef36882 | exact superpose ef36882 ef26
  have ef37216 (X0 X1 X3 X4 : G) : dr X4 (dr X0 X1) = (dr X3 (dr X0 X4)) ◇ (X3 ◇ X1) := by
    first | exact superpose ef151 ef37061 | exact superpose ef37061 ef151
  have ef37339 (X0 X1 X4 : G) : dr X4 (dr X0 X1) = dr X1 (dr X0 X4) := by
    first | exact superpose ef175 ef37216 | exact superpose ef37216 ef175
  have ef99861 : dr x (dr y z) ≠ dr x (dr z y) := by
    first | exact superpose ef37339 ef18 | exact superpose ef18 ef37339
  subsumption ef99861 ef33040

theorem Equation4364_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4364.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4364.models_iff]
    exact fun x y z ↦
      @aux543_4364R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Equation 4380 `x ◇ (x ◇ x) = (x ◇ x) ◇ x` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4380R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    dr x (dr x x) = dr (dr x x) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x (dr x x) ≠ dr (dr x x) x := mod_symm nh
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef157 (X0 X1 : G) : dr X0 X1 = dr X1 X0 := by
    first | exact superpose ef109 ef15 | exact superpose ef15 ef109
  have ef605 : dr x (dr x x) ≠ dr x (dr x x) := by
    first | exact superpose ef157 ef18 | exact superpose ef18 ef157
  exact absurd rfl ef605

theorem Equation4380_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4380.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4380.models_iff]
    exact fun x ↦
      @aux543_4380R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 4396 `x ◇ (x ◇ y) = (x ◇ x) ◇ y` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4396R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x (dr x y) = dr (dr x x) y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : dr x (dr x y) ≠ dr (dr x x) y := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef22 (X0 X1 X2 : G) : X1 ◇ ((dl X1 X0) ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef26 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ (X1 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef37 (X0 X1 X2 : G) : ((dr X0 X1) ◇ (X1 ◇ X2)) ◇ X0 = X2 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef114 (X0 X1 X2 : G) : dr X0 X2 = X1 ◇ ((dl X1 X2) ◇ X0) := by
    first | exact superpose ef14 ef22 | exact superpose ef22 ef14
  have ef151 (X0 X1 : G) : X0 ◇ X1 = dl X0 X1 := by
    first | exact superpose ef19 ef109 | exact superpose ef109 ef19
  have ef808 (X0 X1 X2 : G) : (dl X0 X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef26 ef37 | exact superpose ef37 ef26
  have ef853 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef151 ef808 | exact superpose ef808 ef151
  have ef10281 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ (((dl X2 X1) ◇ X0) ◇ X3) := by
    first | exact superpose ef114 ef24 | exact superpose ef24 ef114
  have ef10352 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ ((dl X2 X1) ◇ (dr X3 X0)) := by
    first | exact superpose ef853 ef10281 | exact superpose ef10281 ef853
  have ef10438 (X0 X1 X3 : G) : dr X3 (dr X0 X1) = dr (dr X3 X0) X1 := by
    first | exact superpose ef114 ef10352 | exact superpose ef10352 ef114
  have ef75110 : dr x (dr x y) ≠ dr x (dr x y) := by
    first | exact superpose ef10438 ef18 | exact superpose ef18 ef10438
  exact absurd rfl ef75110

theorem Equation4396_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4396.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4396.models_iff]
    exact fun x y ↦
      @aux543_4396R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4398 `x ◇ (x ◇ y) = (x ◇ y) ◇ x` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4398R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x (dr x y) = dr (dr x y) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x (dr x y) ≠ dr (dr x y) x := mod_symm nh
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef157 (X0 X1 : G) : dr X0 X1 = dr X1 X0 := by
    first | exact superpose ef109 ef15 | exact superpose ef15 ef109
  have ef605 : dr x (dr x y) ≠ dr x (dr x y) := by
    first | exact superpose ef157 ef18 | exact superpose ef18 ef157
  exact absurd rfl ef605

theorem Equation4398_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4398.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4398.models_iff]
    exact fun x y ↦
      @aux543_4398R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4405 `x ◇ (x ◇ y) = (y ◇ x) ◇ x` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4405R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x (dr x y) = dr (dr y x) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x (dr x y) ≠ dr (dr y x) x := mod_symm nh
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef157 (X0 X1 : G) : dr X0 X1 = dr X1 X0 := by
    first | exact superpose ef109 ef15 | exact superpose ef15 ef109
  have ef607 : dr x (dr x y) ≠ dr x (dr y x) := by
    first | exact superpose ef157 ef18 | exact superpose ef18 ef157
  have ef608 : dr x (dr x y) ≠ dr x (dr x y) := by
    first | exact superpose ef157 ef607 | exact superpose ef607 ef157
  exact absurd rfl ef608

theorem Equation4405_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4405.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4405.models_iff]
    exact fun x y ↦
      @aux543_4405R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4433 `x ◇ (y ◇ x) = (x ◇ x) ◇ y` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4433R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x (dr y x) = dr (dr x x) y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : dr x (dr y x) ≠ dr (dr x x) y := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef22 (X0 X1 X2 : G) : X1 ◇ ((dl X1 X0) ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef25 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X0) = X2 := by
    first | exact superpose ef11 ef11
  have ef26 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ (X1 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef37 (X0 X1 X2 : G) : ((dr X0 X1) ◇ (X1 ◇ X2)) ◇ X0 = X2 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef81 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 X2) ◇ (X2 ◇ X0) := by
    first | exact superpose ef14 ef21 | exact superpose ef21 ef14
  have ef86 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = (dr (X1 ◇ X2) X3) ◇ (X3 ◇ X0) := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef114 (X0 X1 X2 : G) : dr X0 X2 = X1 ◇ ((dl X1 X2) ◇ X0) := by
    first | exact superpose ef14 ef22 | exact superpose ef22 ef14
  have ef151 (X0 X1 : G) : X0 ◇ X1 = dl X0 X1 := by
    first | exact superpose ef19 ef109 | exact superpose ef109 ef19
  have ef159 (X0 X1 X2 : G) : dr X1 X0 = (dr X1 X2) ◇ (X2 ◇ X0) := by
    first | exact superpose ef109 ef21 | exact superpose ef21 ef109
  have ef264 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = (dr X1 X2) ◇ X0 := by
    first | exact superpose ef25 ef21 | exact superpose ef21 ef25
  have ef810 (X0 X1 X2 : G) : (dl X0 X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef26 ef37 | exact superpose ef37 ef26
  have ef855 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef151 ef810 | exact superpose ef810 ef151
  have ef3150 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ ((X2 ◇ X0) ◇ X3) = dr X3 (dr X0 X1) := by
    first | exact superpose ef81 ef24 | exact superpose ef24 ef81
  have ef3180 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X2) := by
    first | exact superpose ef264 ef3150 | exact superpose ef3150 ef264
  have ef3249 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X1 ◇ ((X2 ◇ X0) ◇ (dr X2 X3)) := by
    first | exact superpose ef855 ef3180 | exact superpose ef3180 ef855
  have ef3303 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X1 ◇ (X2 ◇ (dr (dr X2 X3) X0)) := by
    first | exact superpose ef855 ef3249 | exact superpose ef3249 ef855
  have ef10283 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ (((dl X2 X1) ◇ X0) ◇ X3) := by
    first | exact superpose ef114 ef24 | exact superpose ef24 ef114
  have ef10354 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ ((dl X2 X1) ◇ (dr X3 X0)) := by
    first | exact superpose ef855 ef10283 | exact superpose ef10283 ef855
  have ef10440 (X0 X1 X3 : G) : dr X3 (dr X0 X1) = dr (dr X3 X0) X1 := by
    first | exact superpose ef114 ef10354 | exact superpose ef10354 ef114
  have ef32494 (X0 X1 X2 X3 X4 : G) :
      (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) = (dr X0 X2) ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef159 ef86 | exact superpose ef86 ef159
  have ef32551 (X0 X1 X2 X3 X4 : G) :
      (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) = X0 ◇ (((X2 ◇ X1) ◇ X3) ◇ X2) := by
    first | exact superpose ef264 ef32494 | exact superpose ef32494 ef264
  have ef32715 (X0 X1 X2 X3 X4 : G) :
      (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) = X0 ◇ ((X2 ◇ X1) ◇ (dr X2 X3)) := by
    first | exact superpose ef855 ef32551 | exact superpose ef32551 ef855
  have ef32855 (X0 X1 X2 X3 X4 : G) :
      (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) = X0 ◇ (X2 ◇ (dr (dr X2 X3) X1)) := by
    first | exact superpose ef855 ef32715 | exact superpose ef32715 ef855
  have ef32962 (X0 X1 X3 X4 : G) : dr X3 (dr X1 X0) = (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) := by
    first | exact superpose ef3303 ef32855 | exact superpose ef32855 ef3303
  have ef33042 (X0 X1 X3 : G) : dr X3 (dr X0 X1) = dr X3 (dr X1 X0) := by
    first | exact superpose ef81 ef32962 | exact superpose ef32962 ef81
  have ef75112 : dr x (dr y x) ≠ dr x (dr x y) := by
    first | exact superpose ef10440 ef18 | exact superpose ef18 ef10440
  subsumption ef75112 ef33042

theorem Equation4433_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4433.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4433.models_iff]
    exact fun x y ↦
      @aux543_4433R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4435 `x ◇ (y ◇ x) = (x ◇ y) ◇ x` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4435R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x (dr y x) = dr (dr x y) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x (dr y x) ≠ dr (dr x y) x := mod_symm nh
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef157 (X0 X1 : G) : dr X0 X1 = dr X1 X0 := by
    first | exact superpose ef109 ef15 | exact superpose ef15 ef109
  have ef605 : dr x (dr y x) ≠ dr x (dr x y) := by
    first | exact superpose ef157 ef18 | exact superpose ef18 ef157
  have ef606 : dr x (dr x y) ≠ dr x (dr x y) := by
    first | exact superpose ef157 ef605 | exact superpose ef605 ef157
  exact absurd rfl ef606

theorem Equation4435_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4435.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4435.models_iff]
    exact fun x y ↦
      @aux543_4435R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4442 `x ◇ (y ◇ x) = (y ◇ x) ◇ x` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4442R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x (dr y x) = dr (dr y x) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x (dr y x) ≠ dr (dr y x) x := mod_symm nh
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef157 (X0 X1 : G) : dr X0 X1 = dr X1 X0 := by
    first | exact superpose ef109 ef15 | exact superpose ef15 ef109
  have ef607 : dr x (dr y x) ≠ dr x (dr y x) := by
    first | exact superpose ef157 ef18 | exact superpose ef18 ef157
  exact absurd rfl ef607

theorem Equation4442_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4442.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4442.models_iff]
    exact fun x y ↦
      @aux543_4442R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4473 `x ◇ (y ◇ y) = (x ◇ y) ◇ y` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4473R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x (dr y y) = dr (dr x y) y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : dr x (dr y y) ≠ dr (dr x y) y := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef22 (X0 X1 X2 : G) : X1 ◇ ((dl X1 X0) ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef26 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ (X1 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef37 (X0 X1 X2 : G) : ((dr X0 X1) ◇ (X1 ◇ X2)) ◇ X0 = X2 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef114 (X0 X1 X2 : G) : dr X0 X2 = X1 ◇ ((dl X1 X2) ◇ X0) := by
    first | exact superpose ef14 ef22 | exact superpose ef22 ef14
  have ef151 (X0 X1 : G) : X0 ◇ X1 = dl X0 X1 := by
    first | exact superpose ef19 ef109 | exact superpose ef109 ef19
  have ef814 (X0 X1 X2 : G) : (dl X0 X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef26 ef37 | exact superpose ef37 ef26
  have ef859 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef151 ef814 | exact superpose ef814 ef151
  have ef10287 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ (((dl X2 X1) ◇ X0) ◇ X3) := by
    first | exact superpose ef114 ef24 | exact superpose ef24 ef114
  have ef10358 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ ((dl X2 X1) ◇ (dr X3 X0)) := by
    first | exact superpose ef859 ef10287 | exact superpose ef10287 ef859
  have ef10444 (X0 X1 X3 : G) : dr X3 (dr X0 X1) = dr (dr X3 X0) X1 := by
    first | exact superpose ef114 ef10358 | exact superpose ef10358 ef114
  have ef75149 : dr x (dr y y) ≠ dr x (dr y y) := by
    first | exact superpose ef10444 ef18 | exact superpose ef18 ef10444
  exact absurd rfl ef75149

theorem Equation4473_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4473.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4473.models_iff]
    exact fun x y ↦
      @aux543_4473R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4480 `x ◇ (y ◇ y) = (y ◇ x) ◇ y` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4480R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x (dr y y) = dr (dr y x) y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : dr x (dr y y) ≠ dr (dr y x) y := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef22 (X0 X1 X2 : G) : X1 ◇ ((dl X1 X0) ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef26 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ (X1 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef37 (X0 X1 X2 : G) : ((dr X0 X1) ◇ (X1 ◇ X2)) ◇ X0 = X2 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef114 (X0 X1 X2 : G) : dr X0 X2 = X1 ◇ ((dl X1 X2) ◇ X0) := by
    first | exact superpose ef14 ef22 | exact superpose ef22 ef14
  have ef151 (X0 X1 : G) : X0 ◇ X1 = dl X0 X1 := by
    first | exact superpose ef19 ef109 | exact superpose ef109 ef19
  have ef159 (X0 X1 X2 : G) : dr X1 X0 = (dr X1 X2) ◇ (X2 ◇ X0) := by
    first | exact superpose ef109 ef21 | exact superpose ef21 ef109
  have ef366 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X0 = dl X2 (dr X1 X2) := by
    first | exact superpose ef21 ef26 | exact superpose ef26 ef21
  have ef431 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X0 = X2 ◇ (dr X1 X2) := by
    first | exact superpose ef151 ef366 | exact superpose ef366 ef151
  have ef808 (X0 X1 X2 : G) : (dl X0 X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef26 ef37 | exact superpose ef37 ef26
  have ef853 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef151 ef808 | exact superpose ef808 ef151
  have ef10281 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ (((dl X2 X1) ◇ X0) ◇ X3) := by
    first | exact superpose ef114 ef24 | exact superpose ef24 ef114
  have ef10352 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ ((dl X2 X1) ◇ (dr X3 X0)) := by
    first | exact superpose ef853 ef10281 | exact superpose ef10281 ef853
  have ef10438 (X0 X1 X3 : G) : dr X3 (dr X0 X1) = dr (dr X3 X0) X1 := by
    first | exact superpose ef114 ef10352 | exact superpose ef10352 ef114
  have ef32363 (X0 X1 X2 X3 : G) : dr X2 (dr X1 X3) = (dr X2 X3) ◇ ((X0 ◇ X1) ◇ X0) := by
    first | exact superpose ef431 ef159 | exact superpose ef159 ef431
  have ef32667 (X1 X2 X3 : G) : dr X1 (dr X2 X3) = dr X2 (dr X1 X3) := by
    first | exact superpose ef93 ef32363 | exact superpose ef32363 ef93
  have ef75110 : dr x (dr y y) ≠ dr y (dr x y) := by
    first | exact superpose ef10438 ef18 | exact superpose ef18 ef10438
  subsumption ef75110 ef32667

theorem Equation4480_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4480.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4480.models_iff]
    exact fun x y ↦
      @aux543_4480R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4482 `x ◇ (y ◇ y) = (y ◇ y) ◇ x` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4482R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr x (dr y y) = dr (dr y y) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x (dr y y) ≠ dr (dr y y) x := mod_symm nh
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef157 (X0 X1 : G) : dr X0 X1 = dr X1 X0 := by
    first | exact superpose ef109 ef15 | exact superpose ef15 ef109
  have ef605 : dr x (dr y y) ≠ dr x (dr y y) := by
    first | exact superpose ef157 ef18 | exact superpose ef18 ef157
  exact absurd rfl ef605

theorem Equation4482_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4482.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4482.models_iff]
    exact fun x y ↦
      @aux543_4482R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4512 `x ◇ (y ◇ z) = (x ◇ y) ◇ z` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4512R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    dr x (dr y z) = dr (dr x y) z := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : dr x (dr y z) ≠ dr (dr x y) z := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef22 (X0 X1 X2 : G) : X1 ◇ ((dl X1 X0) ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef26 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ (X1 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef37 (X0 X1 X2 : G) : ((dr X0 X1) ◇ (X1 ◇ X2)) ◇ X0 = X2 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef114 (X0 X1 X2 : G) : dr X0 X2 = X1 ◇ ((dl X1 X2) ◇ X0) := by
    first | exact superpose ef14 ef22 | exact superpose ef22 ef14
  have ef151 (X0 X1 : G) : X0 ◇ X1 = dl X0 X1 := by
    first | exact superpose ef19 ef109 | exact superpose ef109 ef19
  have ef808 (X0 X1 X2 : G) : (dl X0 X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef26 ef37 | exact superpose ef37 ef26
  have ef853 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef151 ef808 | exact superpose ef808 ef151
  have ef10281 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ (((dl X2 X1) ◇ X0) ◇ X3) := by
    first | exact superpose ef114 ef24 | exact superpose ef24 ef114
  have ef10352 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ ((dl X2 X1) ◇ (dr X3 X0)) := by
    first | exact superpose ef853 ef10281 | exact superpose ef10281 ef853
  have ef10438 (X0 X1 X3 : G) : dr X3 (dr X0 X1) = dr (dr X3 X0) X1 := by
    first | exact superpose ef114 ef10352 | exact superpose ef10352 ef114
  have ef75110 : dr x (dr y z) ≠ dr x (dr y z) := by
    first | exact superpose ef10438 ef18 | exact superpose ef18 ef10438
  exact absurd rfl ef75110

theorem Equation4512_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4512.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4512.models_iff]
    exact fun x y z ↦
      @aux543_4512R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Equation 4515 `x ◇ (y ◇ z) = (x ◇ z) ◇ y` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4515R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    dr x (dr y z) = dr (dr x z) y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : dr x (dr y z) ≠ dr (dr x z) y := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef22 (X0 X1 X2 : G) : X1 ◇ ((dl X1 X0) ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef25 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X0) = X2 := by
    first | exact superpose ef11 ef11
  have ef26 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ (X1 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef37 (X0 X1 X2 : G) : ((dr X0 X1) ◇ (X1 ◇ X2)) ◇ X0 = X2 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef81 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 X2) ◇ (X2 ◇ X0) := by
    first | exact superpose ef14 ef21 | exact superpose ef21 ef14
  have ef86 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = (dr (X1 ◇ X2) X3) ◇ (X3 ◇ X0) := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef114 (X0 X1 X2 : G) : dr X0 X2 = X1 ◇ ((dl X1 X2) ◇ X0) := by
    first | exact superpose ef14 ef22 | exact superpose ef22 ef14
  have ef151 (X0 X1 : G) : X0 ◇ X1 = dl X0 X1 := by
    first | exact superpose ef19 ef109 | exact superpose ef109 ef19
  have ef159 (X0 X1 X2 : G) : dr X1 X0 = (dr X1 X2) ◇ (X2 ◇ X0) := by
    first | exact superpose ef109 ef21 | exact superpose ef21 ef109
  have ef264 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = (dr X1 X2) ◇ X0 := by
    first | exact superpose ef25 ef21 | exact superpose ef21 ef25
  have ef808 (X0 X1 X2 : G) : (dl X0 X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef26 ef37 | exact superpose ef37 ef26
  have ef853 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef151 ef808 | exact superpose ef808 ef151
  have ef3148 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ ((X2 ◇ X0) ◇ X3) = dr X3 (dr X0 X1) := by
    first | exact superpose ef81 ef24 | exact superpose ef24 ef81
  have ef3178 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X2) := by
    first | exact superpose ef264 ef3148 | exact superpose ef3148 ef264
  have ef3247 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X1 ◇ ((X2 ◇ X0) ◇ (dr X2 X3)) := by
    first | exact superpose ef853 ef3178 | exact superpose ef3178 ef853
  have ef3301 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X1 ◇ (X2 ◇ (dr (dr X2 X3) X0)) := by
    first | exact superpose ef853 ef3247 | exact superpose ef3247 ef853
  have ef10281 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ (((dl X2 X1) ◇ X0) ◇ X3) := by
    first | exact superpose ef114 ef24 | exact superpose ef24 ef114
  have ef10352 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ ((dl X2 X1) ◇ (dr X3 X0)) := by
    first | exact superpose ef853 ef10281 | exact superpose ef10281 ef853
  have ef10438 (X0 X1 X3 : G) : dr X3 (dr X0 X1) = dr (dr X3 X0) X1 := by
    first | exact superpose ef114 ef10352 | exact superpose ef10352 ef114
  have ef32492 (X0 X1 X2 X3 X4 : G) :
      (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) = (dr X0 X2) ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef159 ef86 | exact superpose ef86 ef159
  have ef32549 (X0 X1 X2 X3 X4 : G) :
      (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) = X0 ◇ (((X2 ◇ X1) ◇ X3) ◇ X2) := by
    first | exact superpose ef264 ef32492 | exact superpose ef32492 ef264
  have ef32713 (X0 X1 X2 X3 X4 : G) :
      (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) = X0 ◇ ((X2 ◇ X1) ◇ (dr X2 X3)) := by
    first | exact superpose ef853 ef32549 | exact superpose ef32549 ef853
  have ef32853 (X0 X1 X2 X3 X4 : G) :
      (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) = X0 ◇ (X2 ◇ (dr (dr X2 X3) X1)) := by
    first | exact superpose ef853 ef32713 | exact superpose ef32713 ef853
  have ef32960 (X0 X1 X3 X4 : G) : dr X3 (dr X1 X0) = (dr (dr X0 X1) X4) ◇ (X4 ◇ X3) := by
    first | exact superpose ef3301 ef32853 | exact superpose ef32853 ef3301
  have ef33040 (X0 X1 X3 : G) : dr X3 (dr X0 X1) = dr X3 (dr X1 X0) := by
    first | exact superpose ef81 ef32960 | exact superpose ef32960 ef81
  have ef75110 : dr x (dr y z) ≠ dr x (dr z y) := by
    first | exact superpose ef10438 ef18 | exact superpose ef18 ef10438
  subsumption ef75110 ef33040

theorem Equation4515_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4515.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4515.models_iff]
    exact fun x y z ↦
      @aux543_4515R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Equation 4525 `x ◇ (y ◇ z) = (y ◇ x) ◇ z` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4525R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    dr x (dr y z) = dr (dr y x) z := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : dr x (dr y z) ≠ dr (dr y x) z := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef22 (X0 X1 X2 : G) : X1 ◇ ((dl X1 X0) ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef26 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ (X1 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef37 (X0 X1 X2 : G) : ((dr X0 X1) ◇ (X1 ◇ X2)) ◇ X0 = X2 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef114 (X0 X1 X2 : G) : dr X0 X2 = X1 ◇ ((dl X1 X2) ◇ X0) := by
    first | exact superpose ef14 ef22 | exact superpose ef22 ef14
  have ef151 (X0 X1 : G) : X0 ◇ X1 = dl X0 X1 := by
    first | exact superpose ef19 ef109 | exact superpose ef109 ef19
  have ef159 (X0 X1 X2 : G) : dr X1 X0 = (dr X1 X2) ◇ (X2 ◇ X0) := by
    first | exact superpose ef109 ef21 | exact superpose ef21 ef109
  have ef366 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X0 = dl X2 (dr X1 X2) := by
    first | exact superpose ef21 ef26 | exact superpose ef26 ef21
  have ef431 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X0 = X2 ◇ (dr X1 X2) := by
    first | exact superpose ef151 ef366 | exact superpose ef366 ef151
  have ef814 (X0 X1 X2 : G) : (dl X0 X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef26 ef37 | exact superpose ef37 ef26
  have ef859 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef151 ef814 | exact superpose ef814 ef151
  have ef10287 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ (((dl X2 X1) ◇ X0) ◇ X3) := by
    first | exact superpose ef114 ef24 | exact superpose ef24 ef114
  have ef10358 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ ((dl X2 X1) ◇ (dr X3 X0)) := by
    first | exact superpose ef859 ef10287 | exact superpose ef10287 ef859
  have ef10444 (X0 X1 X3 : G) : dr X3 (dr X0 X1) = dr (dr X3 X0) X1 := by
    first | exact superpose ef114 ef10358 | exact superpose ef10358 ef114
  have ef32369 (X0 X1 X2 X3 : G) : dr X2 (dr X1 X3) = (dr X2 X3) ◇ ((X0 ◇ X1) ◇ X0) := by
    first | exact superpose ef431 ef159 | exact superpose ef159 ef431
  have ef32673 (X1 X2 X3 : G) : dr X1 (dr X2 X3) = dr X2 (dr X1 X3) := by
    first | exact superpose ef93 ef32369 | exact superpose ef32369 ef93
  have ef75116 : dr x (dr y z) ≠ dr y (dr x z) := by
    first | exact superpose ef10444 ef18 | exact superpose ef18 ef10444
  subsumption ef75116 ef32673

theorem Equation4525_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4525.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4525.models_iff]
    exact fun x y z ↦
      @aux543_4525R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Equation 4531 `x ◇ (y ◇ z) = (y ◇ z) ◇ x` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4531R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    dr x (dr y z) = dr (dr y z) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x (dr y z) ≠ dr (dr y z) x := mod_symm nh
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef157 (X0 X1 : G) : dr X0 X1 = dr X1 X0 := by
    first | exact superpose ef109 ef15 | exact superpose ef15 ef109
  have ef605 : dr x (dr y z) ≠ dr x (dr y z) := by
    first | exact superpose ef157 ef18 | exact superpose ef18 ef157
  exact absurd rfl ef605

theorem Equation4531_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4531.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4531.models_iff]
    exact fun x y z ↦
      @aux543_4531R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Equation 4541 `x ◇ (y ◇ z) = (z ◇ x) ◇ y` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4541R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    dr x (dr y z) = dr (dr z x) y := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : dr x (dr y z) ≠ dr (dr z x) y := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef22 (X0 X1 X2 : G) : X1 ◇ ((dl X1 X0) ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef26 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ (X1 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef37 (X0 X1 X2 : G) : ((dr X0 X1) ◇ (X1 ◇ X2)) ◇ X0 = X2 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef81 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 X2) ◇ (X2 ◇ X0) := by
    first | exact superpose ef14 ef21 | exact superpose ef21 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef114 (X0 X1 X2 : G) : dr X0 X2 = X1 ◇ ((dl X1 X2) ◇ X0) := by
    first | exact superpose ef14 ef22 | exact superpose ef22 ef14
  have ef151 (X0 X1 : G) : X0 ◇ X1 = dl X0 X1 := by
    first | exact superpose ef19 ef109 | exact superpose ef109 ef19
  have ef159 (X0 X1 X2 : G) : dr X1 X0 = (dr X1 X2) ◇ (X2 ◇ X0) := by
    first | exact superpose ef109 ef21 | exact superpose ef21 ef109
  have ef814 (X0 X1 X2 : G) : (dl X0 X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef26 ef37 | exact superpose ef37 ef26
  have ef859 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef151 ef814 | exact superpose ef814 ef151
  have ef3128 (X0 X1 X2 : G) : dr X1 X2 = X2 ◇ (X0 ◇ (dr X0 X1)) := by
    first | exact superpose ef81 ef11 | exact superpose ef11 ef81
  have ef10287 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ (((dl X2 X1) ◇ X0) ◇ X3) := by
    first | exact superpose ef114 ef24 | exact superpose ef24 ef114
  have ef10358 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ ((dl X2 X1) ◇ (dr X3 X0)) := by
    first | exact superpose ef859 ef10287 | exact superpose ef10287 ef859
  have ef10444 (X0 X1 X3 : G) : dr X3 (dr X0 X1) = dr (dr X3 X0) X1 := by
    first | exact superpose ef114 ef10358 | exact superpose ef10358 ef114
  have ef57752 (X0 X1 X2 : G) : dr X1 (dr X2 X0) = dr X0 (dr X1 X2) := by
    first | exact superpose ef3128 ef159 | exact superpose ef159 ef3128
  have ef75116 : dr x (dr y z) ≠ dr z (dr x y) := by
    first | exact superpose ef10444 ef18 | exact superpose ef18 ef10444
  subsumption ef75116 ef57752

theorem Equation4541_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4541.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4541.models_iff]
    exact fun x y z ↦
      @aux543_4541R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Equation 4544 `x ◇ (y ◇ z) = (z ◇ y) ◇ x` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4544R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    dr x (dr y z) = dr (dr z y) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr x (dr y z) ≠ dr (dr z y) x := mod_symm nh
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef157 (X0 X1 : G) : dr X0 X1 = dr X1 X0 := by
    first | exact superpose ef109 ef15 | exact superpose ef15 ef109
  have ef607 : dr x (dr y z) ≠ dr (dr y z) x := by
    first | exact superpose ef157 ef18 | exact superpose ef18 ef157
  subsumption ef607 ef157

theorem Equation4544_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4544.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4544.models_iff]
    exact fun x y z ↦
      @aux543_4544R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Equation 4635 `(x ◇ y) ◇ x = (y ◇ x) ◇ x` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4635R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr (dr x y) x = dr (dr y x) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr (dr x y) x ≠ dr (dr y x) x := mod_symm nh
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef157 (X0 X1 : G) : dr X0 X1 = dr X1 X0 := by
    first | exact superpose ef109 ef15 | exact superpose ef15 ef109
  have ef606 : dr (dr x y) x ≠ dr (dr x y) x := by
    first | exact superpose ef157 ef18 | exact superpose ef18 ef157
  exact absurd rfl ef606

theorem Equation4635_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4635.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4635.models_iff]
    exact fun x y ↦
      @aux543_4635R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4677 `(x ◇ y) ◇ z = (y ◇ x) ◇ z` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4677R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    dr (dr x y) z = dr (dr y x) z := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 : dr (dr x y) z ≠ dr (dr y x) z := mod_symm nh
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef157 (X0 X1 : G) : dr X0 X1 = dr X1 X0 := by
    first | exact superpose ef109 ef15 | exact superpose ef15 ef109
  have ef607 : dr (dr x y) z ≠ dr (dr x y) z := by
    first | exact superpose ef157 ef18 | exact superpose ef18 ef157
  exact absurd rfl ef607

theorem Equation4677_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4677.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4677.models_iff]
    exact fun x y z ↦
      @aux543_4677R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

set_option maxHeartbeats 600000 in
/-- Equation 4679 `(x ◇ y) ◇ z = (y ◇ z) ◇ x` holds of the right division of any magma satisfying
equation 543 `x = y ◇ (z ◇ (x ◇ (y ◇ z)))` and equipped with two-sided divisions. -/
private theorem aux543_4679R [Finite G] [Magma G] (h : Equation543 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    dr (dr x y) z = dr (dr y z) x := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (c ◇ a)) ◇ (b ◇ c) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (c ◇ z)) (g := fun z ↦ z ◇ (b ◇ c))
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : c ◇ ((b ◇ a) ◇ (b ◇ c)) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ c)) (g := fun z ↦ c ◇ z)
      (fun z ↦ hrot0 z b c) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2) = X0 := mod_symm (hrot0 ..)
  have ef13 (X0 X1 X2 : G) : X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (hrot1 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : dr (dr x y) z ≠ dr (dr y z) x := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef21 (X0 X1 X2 : G) : (dr X0 X1) ◇ (X1 ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef22 (X0 X1 X2 : G) : X1 ◇ ((dl X1 X0) ◇ (X2 ◇ X0)) = X2 := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef24 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X0 (X1 ◇ X2) := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef25 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X0) = X2 := by
    first | exact superpose ef11 ef11
  have ef26 (X0 X1 X2 : G) : X2 ◇ (X0 ◇ (X1 ◇ X2)) = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef32 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ (X1 ◇ X2) = dl X2 X0 := by
    first | exact superpose ef16 ef12 | exact superpose ef12 ef16
  have ef37 (X0 X1 X2 : G) : ((dr X0 X1) ◇ (X1 ◇ X2)) ◇ X0 = X2 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef59 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) = X3 := by
    first | exact superpose ef12 ef13 | exact superpose ef13 ef12
  have ef81 (X0 X1 X2 : G) : dr X0 X1 = (dr X1 X2) ◇ (X2 ◇ X0) := by
    first | exact superpose ef14 ef21 | exact superpose ef21 ef14
  have ef91 (X0 X1 X2 : G) : (dr X1 (X2 ◇ (X1 ◇ X0))) ◇ X0 = X2 := by
    first | exact superpose ef12 ef21 | exact superpose ef21 ef12
  have ef93 (X0 X1 X2 : G) : dr X2 X1 = X1 ◇ ((X0 ◇ X2) ◇ X0) := by
    first | exact superpose ef21 ef11 | exact superpose ef11 ef21
  have ef104 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0 = X2 := by
    first | exact superpose ef24 ef91 | exact superpose ef91 ef24
  have ef109 (X0 X2 : G) : (dr X0 X2) ◇ X0 = X2 := by
    first | exact superpose ef93 ef104 | exact superpose ef104 ef93
  have ef114 (X0 X1 X2 : G) : dr X0 X2 = X1 ◇ ((dl X1 X2) ◇ X0) := by
    first | exact superpose ef14 ef22 | exact superpose ef22 ef14
  have ef151 (X0 X1 : G) : X0 ◇ X1 = dl X0 X1 := by
    first | exact superpose ef19 ef109 | exact superpose ef109 ef19
  have ef159 (X0 X1 X2 : G) : dr X1 X0 = (dr X1 X2) ◇ (X2 ◇ X0) := by
    first | exact superpose ef109 ef21 | exact superpose ef21 ef109
  have ef163 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr (X1 ◇ X2) X0 := by
    first | exact superpose ef109 ef11 | exact superpose ef11 ef109
  have ef264 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ X2) = (dr X1 X2) ◇ X0 := by
    first | exact superpose ef25 ef21 | exact superpose ef21 ef25
  have ef365 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = dl (X1 ◇ (X2 ◇ X0)) X3 := by
    first | exact superpose ef12 ef26 | exact superpose ef26 ef12
  have ef432 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (X3 ◇ X0) = (X1 ◇ (X2 ◇ X0)) ◇ X3 := by
    first | exact superpose ef151 ef365 | exact superpose ef365 ef151
  have ef810 (X0 X1 X2 : G) : (dl X0 X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef26 ef37 | exact superpose ef37 ef26
  have ef855 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = X0 ◇ (dr X2 X1) := by
    first | exact superpose ef151 ef810 | exact superpose ef810 ef151
  have ef3124 (X0 X1 X2 : G) : dr X1 X2 = X2 ◇ (X0 ◇ (dr X0 X1)) := by
    first | exact superpose ef81 ef11 | exact superpose ef11 ef81
  have ef3150 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ ((X2 ◇ X0) ◇ X3) = dr X3 (dr X0 X1) := by
    first | exact superpose ef81 ef24 | exact superpose ef24 ef81
  have ef3180 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X2) := by
    first | exact superpose ef264 ef3150 | exact superpose ef3150 ef264
  have ef3249 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X1 ◇ ((X2 ◇ X0) ◇ (dr X2 X3)) := by
    first | exact superpose ef855 ef3180 | exact superpose ef3180 ef855
  have ef3303 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X1 ◇ (X2 ◇ (dr (dr X2 X3) X0)) := by
    first | exact superpose ef855 ef3249 | exact superpose ef3249 ef855
  have ef8270 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = dl (((X1 ◇ (X2 ◇ X4)) ◇ X0) ◇ X4) X3 := by
    first | exact superpose ef59 ef32 | exact superpose ef32 ef59
  have ef8321 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = (((X1 ◇ (X2 ◇ X4)) ◇ X0) ◇ X4) ◇ X3 := by
    first | exact superpose ef151 ef8270 | exact superpose ef8270 ef151
  have ef8494 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = ((X1 ◇ (X2 ◇ X4)) ◇ X0) ◇ (dr X3 X4) := by
    first | exact superpose ef855 ef8321 | exact superpose ef8321 ef855
  have ef8652 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = (X1 ◇ (X2 ◇ X4)) ◇ (dr (dr X3 X4) X0) := by
    first | exact superpose ef855 ef8494 | exact superpose ef8494 ef855
  have ef8793 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = (X1 ◇ X2) ◇ ((dr (dr X3 X4) X0) ◇ X4) := by
    first | exact superpose ef432 ef8652 | exact superpose ef8652 ef432
  have ef8924 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ (dr ((dr (dr X3 X4) X0) ◇ X4) X2) := by
    first | exact superpose ef855 ef8793 | exact superpose ef8793 ef855
  have ef9037 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ ((dr (dr X3 X4) X0) ◇ (X4 ◇ X2)) := by
    first | exact superpose ef163 ef8924 | exact superpose ef8924 ef163
  have ef9129 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ ((dr X3 X4) ◇ ((X4 ◇ X2) ◇ X0)) := by
    first | exact superpose ef264 ef9037 | exact superpose ef9037 ef264
  have ef9209 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ (X3 ◇ (((X4 ◇ X2) ◇ X0) ◇ X4)) := by
    first | exact superpose ef264 ef9129 | exact superpose ef9129 ef264
  have ef9274 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ (X3 ◇ ((X4 ◇ X2) ◇ (dr X4 X0))) := by
    first | exact superpose ef855 ef9209 | exact superpose ef9209 ef855
  have ef9327 (X0 X1 X2 X3 X4 : G) :
      ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ (X3 ◇ (X4 ◇ (dr (dr X4 X0) X2))) := by
    first | exact superpose ef855 ef9274 | exact superpose ef9274 ef855
  have ef9373 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) ◇ X0 = X1 ◇ (dr X0 (dr X2 X3)) := by
    first | exact superpose ef3303 ef9327 | exact superpose ef9327 ef3303
  have ef9413 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ (dr X0 X3) = X1 ◇ (dr X0 (dr X2 X3)) := by
    first | exact superpose ef855 ef9373 | exact superpose ef9373 ef855
  have ef9441 (X0 X1 X2 X3 : G) : X1 ◇ (dr (dr X0 X3) X2) = X1 ◇ (dr X0 (dr X2 X3)) := by
    first | exact superpose ef855 ef9413 | exact superpose ef9413 ef855
  have ef10283 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ (((dl X2 X1) ◇ X0) ◇ X3) := by
    first | exact superpose ef114 ef24 | exact superpose ef24 ef114
  have ef10354 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X2 ◇ ((dl X2 X1) ◇ (dr X3 X0)) := by
    first | exact superpose ef855 ef10283 | exact superpose ef10283 ef855
  have ef10440 (X0 X1 X3 : G) : dr X3 (dr X0 X1) = dr (dr X3 X0) X1 := by
    first | exact superpose ef114 ef10354 | exact superpose ef10354 ef114
  have ef32469 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = (dr X0 X2) ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef159 ef24 | exact superpose ef24 ef159
  have ef32576 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X0 ◇ (((X2 ◇ X1) ◇ X3) ◇ X2) := by
    first | exact superpose ef264 ef32469 | exact superpose ef32469 ef264
  have ef32740 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X0 ◇ ((X2 ◇ X1) ◇ (dr X2 X3)) := by
    first | exact superpose ef855 ef32576 | exact superpose ef32576 ef855
  have ef32877 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X0 ◇ (X2 ◇ (dr (dr X2 X3) X1)) := by
    first | exact superpose ef855 ef32740 | exact superpose ef32740 ef855
  have ef32980 (X0 X1 X2 X3 : G) : dr X3 (dr X0 X1) = X0 ◇ (X2 ◇ (dr X2 (dr X1 X3))) := by
    first | exact superpose ef9441 ef32877 | exact superpose ef32877 ef9441
  have ef33057 (X0 X1 X3 : G) : dr X3 (dr X0 X1) = dr (dr X1 X3) X0 := by
    first | exact superpose ef3124 ef32980 | exact superpose ef32980 ef3124
  have ef75112 : dr (dr x y) z ≠ dr y (dr z x) := by
    first | exact superpose ef10440 ef18 | exact superpose ef18 ef10440
  subsumption ef75112 ef33057

theorem Equation4679_termStructuralFromFin_Equation543_finiteDivisionR :
    Law4679.TermStructuralFromFin Law543 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj543R G _ M (Law543.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj543L G _ M (Law543.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4679.models_iff]
    exact fun x y z ↦
      @aux543_4679R G _ M (Law543.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

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

theorem Equation556_termStructuralFromFin_Equation546_finiteDivisionL :
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

theorem Equation546_termStructuralFromFin_Equation556_finiteDivisionL :
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

/-- Left translation by `t` is injective in every finite magma satisfying equation 670
`x = y ◇ (x ◇ ((x ◇ y) ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj670L [Finite G] [Magma G] (h : Equation670 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ (((b ◇ a) ◇ b) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ ((z ◇ b) ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef13 : q = (t ◇ p) ◇ (((t ◇ p) ◇ t) ◇ t) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef16 : p = q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef16 ef10

/-- Equation 99 `x = x ◇ ((x ◇ x) ◇ x)` holds of the left division of any magma satisfying equation
670 `x = y ◇ (x ◇ ((x ◇ y) ◇ y))` and equipped with that one division. -/
private theorem aux670_99L1 [Finite G] [Magma G] (h : Equation670 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl x (dl (dl x x) x) := by
  by_contra nh
  have ef8 (X0 X1 : G) : X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have ef10 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef11 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef12 : x ≠ dl x (dl (dl x x) x) := mod_symm nh
  have ef13 (X0 X1 : G) : (dl X1 X0) ◇ (X1 ◇ (X0 ◇ (dl X1 X0))) = X1 := by
    first | exact superpose ef10 ef8 | exact superpose ef8 ef10
  have ef52 (X0 : G) : (dl X0 X0) ◇ (X0 ◇ X0) = X0 := by
    first | exact superpose ef10 ef13 | exact superpose ef13 ef10
  have ef65 (X0 : G) : X0 ◇ X0 = dl (dl X0 X0) X0 := by
    first | exact superpose ef52 ef11 | exact superpose ef11 ef52
  have ef94 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef65 ef12 | exact superpose ef12 ef65
  subsumption ef94 ef11

theorem Equation99_termStructuralFromFin_Equation670_finiteDivisionL :
    Law99.TermStructuralFromFin Law670 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj670L G _ M (Law670.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law99.models_iff]
    exact fun x ↦
      @aux670_99L1 G _ M (Law670.models_iff.mp hGL) dl h1 h2 x

/-- Left translation by `t` is injective in every finite magma satisfying equation 676
`x = y ◇ (x ◇ ((y ◇ x) ◇ x))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj676L [Finite G] [Magma G] (h : Equation676 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ (b ◇ a)) ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ ((b ◇ z) ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef14 : q = (t ◇ p) ◇ ((t ◇ (t ◇ p)) ◇ (t ◇ p)) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef17 : p = q := by
    first | exact superpose ef8 ef14 | exact superpose ef14 ef8
  subsumption ef17 ef10

/-- Equation 1426 `x = (x ◇ x) ◇ (x ◇ (x ◇ x))` holds of the left division of any magma satisfying
equation 676 `x = y ◇ (x ◇ ((y ◇ x) ◇ x))` and equipped with that one division. -/
private theorem aux676_1426L1 [Finite G] [Magma G] (h : Equation676 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl (dl x x) (dl x (dl x x)) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ (b ◇ a)) ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ ((b ◇ z) ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := mod_symm (h ..)
  have ef9 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef11 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef12 : x ≠ dl (dl x x) (dl x (dl x x)) := mod_symm nh
  have ef15 (X0 X1 : G) : X0 ◇ ((X1 ◇ X0) ◇ X0) = dl X1 X0 := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  have ef22 (X0 X1 : G) : (X0 ◇ X1) ◇ X1 = dl X1 (dl X0 X1) := by
    first | exact superpose ef15 ef11 | exact superpose ef11 ef15
  have ef24 (X0 : G) :
      (X0 ◇ X0) ◇ X0 = (X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    first | exact superpose ef8 ef9 | exact superpose ef9 ef8
  have ef37 (X0 : G) : (X0 ◇ X0) ◇ X0 = (X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0 := by
    first | exact superpose ef8 ef24 | exact superpose ef24 ef8
  have ef38 (X0 : G) : (X0 ◇ X0) ◇ X0 = (dl X0 X0) ◇ X0 := by
    first | exact superpose ef15 ef37 | exact superpose ef37 ef15
  have ef42 (X0 : G) : dl (dl X0 X0) ((X0 ◇ X0) ◇ X0) = X0 := by
    first | exact superpose ef38 ef11 | exact superpose ef11 ef38
  have ef58 : x ≠ dl (dl x x) ((x ◇ x) ◇ x) := by
    first | exact superpose ef22 ef12 | exact superpose ef12 ef22
  subsumption ef58 ef42

theorem Equation1426_termStructuralFromFin_Equation676_finiteDivisionL :
    Law1426.TermStructuralFromFin Law676 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj676L G _ M (Law676.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law1426.models_iff]
    exact fun x ↦
      @aux676_1426L1 G _ M (Law676.models_iff.mp hGL) dl h1 h2 x

/-- Left translation by `t` is injective in every finite magma satisfying equation 680
`x = y ◇ (x ◇ ((y ◇ y) ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj680L [Finite G] [Magma G] (h : Equation680 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ b) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ ((b ◇ b) ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef12 : q = (t ◇ p) ◇ ((t ◇ t) ◇ t) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef14 : p = q := by
    first | exact superpose ef8 ef12 | exact superpose ef12 ef8
  subsumption ef14 ef10

/-- Right translation by `t` is injective in every finite magma satisfying equation 680
`x = y ◇ (x ◇ ((y ◇ y) ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj680R [Finite G] [Magma G] (h : Equation680 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ b) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ ((b ◇ b) ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef9 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 (X0 : G) : ((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    first | exact superpose ef7 ef7
  have ef12 : t = (p ◇ t) ◇ ((q ◇ q) ◇ q) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef13 (X0 X1 : G) : (X1 ◇ X1) ◇ X1 = X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef8 ef8
  have ef15 : (q ◇ q) ◇ q = t ◇ (((p ◇ t) ◇ (p ◇ t)) ◇ (p ◇ t)) := by
    first | exact superpose ef12 ef8 | exact superpose ef8 ef12
  have ef16 : (q ◇ q) ◇ q = (p ◇ p) ◇ p := by
    first | exact superpose ef13 ef15 | exact superpose ef15 ef13
  have ef19 : q = ((p ◇ p) ◇ p) ◇ (((p ◇ p) ◇ p) ◇ ((p ◇ p) ◇ p)) := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef23 : p = q := by
    first | exact superpose ef11 ef19 | exact superpose ef19 ef11
  subsumption ef23 ef10

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` holds of the left division of any magma satisfying
equation 680 `x = y ◇ (x ◇ ((y ◇ y) ◇ y))` and equipped with two-sided divisions. -/
private theorem aux680_4273L [Finite G] [Magma G] (h : Equation680 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dl x (dl x x) = dl y (dl x y) := by
  by_contra nh
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dl x (dl x x) ≠ dl y (dl x y) := mod_symm nh
  have ef21 (X0 X1 : G) : X0 ◇ ((X1 ◇ X1) ◇ X1) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef55 (X0 X1 : G) : (X0 ◇ X0) ◇ X0 = dl X1 (dl X0 X1) := by
    first | exact superpose ef21 ef15 | exact superpose ef15 ef21
  have ef150 : dl x (dl x x) ≠ (x ◇ x) ◇ x := by
    first | exact superpose ef55 ef16 | exact superpose ef16 ef55
  subsumption ef150 ef55

theorem Equation4273_termStructuralFromFin_Equation680_finiteDivisionL :
    Law4273.TermStructuralFromFin Law680 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj680R G _ M (Law680.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj680L G _ M (Law680.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4273.models_iff]
    exact fun x y ↦
      @aux680_4273L G _ M (Law680.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4588 `(x ◇ x) ◇ x = (y ◇ x) ◇ y` holds of the right division of any magma satisfying
equation 680 `x = y ◇ (x ◇ ((y ◇ y) ◇ y))` and equipped with two-sided divisions. -/
private theorem aux680_4588R [Finite G] [Magma G] (h : Equation680 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr (dr x x) x = dr (dr y x) y := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ b) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ ((b ◇ b) ◇ b))
      (fun z ↦ (h z b).symm) a
  have ef10 (X0 X1 : G) : X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1) = X0 := mod_symm (hrot0 ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dr (dr x x) x ≠ dr (dr y x) y := mod_symm nh
  have ef19 (X0 X1 : G) : X1 ◇ X0 = dr X0 ((X1 ◇ X1) ◇ X1) := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef21 (X0 X1 : G) : X0 ◇ ((X1 ◇ X1) ◇ X1) = dl X1 X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef29 (X0 X1 : G) : (X1 ◇ X1) ◇ X1 = dl (X1 ◇ X0) X0 := by
    first | exact superpose ef11 ef15 | exact superpose ef15 ef11
  have ef55 (X0 X1 : G) : (X0 ◇ X0) ◇ X0 = dl X1 (dl X0 X1) := by
    first | exact superpose ef21 ef15 | exact superpose ef15 ef21
  have ef102 (X0 X1 : G) : dl (X0 ◇ X0) (dl (X0 ◇ X1) X1) = X0 := by
    first | exact superpose ef29 ef15 | exact superpose ef15 ef29
  have ef137 (X0 X1 X2 : G) : X1 ◇ X2 = dr X2 (dl X0 (dl X1 X0)) := by
    first | exact superpose ef55 ef19 | exact superpose ef19 ef55
  have ef532 (X0 X1 : G) : dr X1 X0 = (X0 ◇ (X0 ◇ X0)) ◇ X1 := by
    first | exact superpose ef102 ef137 | exact superpose ef137 ef102
  have ef2595 (X0 X1 : G) : X1 ◇ (X1 ◇ X1) = dr (dr X0 X1) X0 := by
    first | exact superpose ef532 ef13 | exact superpose ef13 ef532
  have ef5821 : dr (dr x x) x ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef2595 ef16 | exact superpose ef16 ef2595
  subsumption ef5821 ef2595

theorem Equation4588_termStructuralFromFin_Equation680_finiteDivisionR :
    Law4588.TermStructuralFromFin Law680 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj680R G _ M (Law680.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj680L G _ M (Law680.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4588.models_iff]
    exact fun x y ↦
      @aux680_4588R G _ M (Law680.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Left translation by `t` is injective in every finite magma satisfying equation 704
`x = y ◇ (y ◇ ((x ◇ x) ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj704L [Finite G] [Magma G] (h : Equation704 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (a ◇ b))) ◇ (b ◇ (b ◇ (a ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ (z ◇ b))) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ (b ◇ a)) ◇ (b ◇ (b ◇ a))) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ (b ◇ (b ◇ z))) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have hrot2 (a b : G) : b ◇ (((b ◇ a) ◇ (b ◇ a)) ◇ b) = a :=
    rot_of_finite (f := fun z ↦ ((b ◇ z) ◇ (b ◇ z)) ◇ b) (g := fun z ↦ b ◇ z)
      (fun z ↦ hrot1 z b) a
  have ef12 (X0 X1 : G) : X1 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (hrot2 ..)
  have ef13 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef14 : p ≠ q := mod_symm nh
  have ef16 : q = t ◇ (((t ◇ p) ◇ (t ◇ p)) ◇ t) := by
    first | exact superpose ef13 ef12 | exact superpose ef12 ef13
  have ef19 : p = q := by
    first | exact superpose ef12 ef16 | exact superpose ef16 ef12
  subsumption ef19 ef14

/-- Right translation by `t` is injective in every finite magma satisfying equation 704
`x = y ◇ (y ◇ ((x ◇ x) ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj704R [Finite G] [Magma G] (h : Equation704 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (a ◇ b))) ◇ (b ◇ (b ◇ (a ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ (z ◇ b))) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef10 (X0 X1 : G) :
      (X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (hrot0 ..)
  have ef13 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef14 : p ≠ q := mod_symm nh
  have ef29 : q = (t ◇ (t ◇ (p ◇ t))) ◇ (t ◇ (t ◇ (p ◇ t))) := by
    first | exact superpose ef13 ef10 | exact superpose ef10 ef13
  have ef41 : p = q := by
    first | exact superpose ef10 ef29 | exact superpose ef29 ef10
  subsumption ef41 ef14

/-- Equation 203 `x = (x ◇ (x ◇ x)) ◇ x` holds of the right division of any magma satisfying
equation 704 `x = y ◇ (y ◇ ((x ◇ x) ◇ y))` and equipped with two-sided divisions. -/
private theorem aux704_203R [Finite G] [Magma G] (h : Equation704 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dr (dr x (dr x x)) x := by
  by_contra nh
  have ef12 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := mod_symm (h ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 : x ≠ dr (dr x (dr x x)) x := mod_symm nh
  have ef21 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef18 ef17 | exact superpose ef17 ef18
  have ef22 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef16 ef19 | exact superpose ef19 ef16
  have ef25 (X0 X1 : G) : X1 ◇ ((X0 ◇ X0) ◇ X1) = dl X1 X0 := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef65 (X0 X1 : G) : (X1 ◇ X1) ◇ X0 = dl X0 (dl X0 X1) := by
    first | exact superpose ef25 ef19 | exact superpose ef19 ef25
  have ef153 (X0 X1 : G) : dl (X1 ◇ X1) (dl X0 (dl X0 X1)) = X0 := by
    first | exact superpose ef65 ef19 | exact superpose ef19 ef65
  have ef223 (X0 X1 : G) : dr X1 X0 = dl (X1 ◇ X1) (dl (dr X1 X0) X0) := by
    first | exact superpose ef22 ef153 | exact superpose ef153 ef22
  have ef784 (X0 : G) : dl (X0 ◇ X0) X0 = dr X0 X0 := by
    first | exact superpose ef22 ef223 | exact superpose ef223 ef22
  have ef860 (X0 : G) : X0 ◇ X0 = dr X0 (dr X0 X0) := by
    first | exact superpose ef784 ef21 | exact superpose ef21 ef784
  have ef1025 : x ≠ dr (x ◇ x) x := by
    first | exact superpose ef860 ef20 | exact superpose ef20 ef860
  subsumption ef1025 ef17

theorem Equation203_termStructuralFromFin_Equation704_finiteDivisionR :
    Law203.TermStructuralFromFin Law704 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj704R G _ M (Law704.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj704L G _ M (Law704.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law203.models_iff]
    exact fun x ↦
      @aux704_203R G _ M (Law704.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Left translation by `t` is injective in every finite magma satisfying equation 707
`x = y ◇ (y ◇ ((x ◇ y) ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj707L [Finite G] [Magma G] (h : Equation707 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (a ◇ b))) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ (z ◇ b))) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ (b ◇ a)) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef11 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef13 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef14 : p ≠ q := mod_symm nh
  have ef22 : q = ((t ◇ (t ◇ p)) ◇ t) ◇ t := by
    first | exact superpose ef13 ef11 | exact superpose ef11 ef13
  have ef28 : p = q := by
    first | exact superpose ef11 ef22 | exact superpose ef22 ef11
  subsumption ef28 ef14

/-- Right translation by `t` is injective in every finite magma satisfying equation 707
`x = y ◇ (y ◇ ((x ◇ y) ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj707R [Finite G] [Magma G] (h : Equation707 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have ef9 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have ef13 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef14 : p ≠ q := mod_symm nh
  have ef15 : q = t ◇ (t ◇ ((p ◇ t) ◇ t)) := by
    first | exact superpose ef13 ef9 | exact superpose ef9 ef13
  have ef17 : p = q := by
    first | exact superpose ef9 ef15 | exact superpose ef15 ef9
  subsumption ef17 ef14

/-- Equation 1629 `x = (x ◇ x) ◇ ((x ◇ x) ◇ x)` holds of the left division of any magma satisfying
equation 707 `x = y ◇ (y ◇ ((x ◇ y) ◇ y))` and equipped with two-sided divisions. -/
private theorem aux707_1629L [Finite G] [Magma G] (h : Equation707 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl (dl x x) (dl (dl x x) x) := by
  by_contra nh
  have ef12 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 : x ≠ dl (dl x x) (dl (dl x x) x) := mod_symm nh
  have ef26 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ X1) = dl X1 X0 := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef122 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = dl X0 (dl X0 X1) := by
    first | exact superpose ef26 ef19 | exact superpose ef19 ef26
  have ef398 : x ≠ (x ◇ (dl x x)) ◇ (dl x x) := by
    first | exact superpose ef122 ef20 | exact superpose ef20 ef122
  have ef406 : x ≠ x ◇ (dl x x) := by
    first | exact superpose ef18 ef398 | exact superpose ef398 ef18
  subsumption ef406 ef18

theorem Equation1629_termStructuralFromFin_Equation707_finiteDivisionL :
    Law1629.TermStructuralFromFin Law707 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj707R G _ M (Law707.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj707L G _ M (Law707.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1629.models_iff]
    exact fun x ↦
      @aux707_1629L G _ M (Law707.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 1832 `x = (x ◇ (x ◇ x)) ◇ (x ◇ x)` holds of the left division of any magma satisfying
equation 707 `x = y ◇ (y ◇ ((x ◇ y) ◇ y))` and equipped with two-sided divisions. -/
private theorem aux707_1832L [Finite G] [Magma G] (h : Equation707 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl (dl x (dl x x)) (dl x x) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (a ◇ b))) ◇ b = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ (z ◇ b))) (g := fun z ↦ z ◇ b)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ (b ◇ a)) ◇ b) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ b) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef12 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 : x ≠ dl (dl x (dl x x)) (dl x x) := mod_symm nh
  have ef26 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ X1) = dl X1 X0 := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) ◇ X1 = dl X1 X0 := by
    first | exact superpose ef18 ef14 | exact superpose ef14 ef18
  have ef122 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = dl X0 (dl X0 X1) := by
    first | exact superpose ef26 ef19 | exact superpose ef19 ef26
  have ef211 (X0 X1 : G) : dl ((X0 ◇ X1) ◇ X0) (dl X0 X1) = X0 := by
    first | exact superpose ef43 ef19 | exact superpose ef19 ef43
  have ef403 : x ≠ dl ((x ◇ x) ◇ x) (dl x x) := by
    first | exact superpose ef122 ef20 | exact superpose ef20 ef122
  subsumption ef403 ef211

theorem Equation1832_termStructuralFromFin_Equation707_finiteDivisionL :
    Law1832.TermStructuralFromFin Law707 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj707R G _ M (Law707.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj707L G _ M (Law707.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1832.models_iff]
    exact fun x ↦
      @aux707_1832L G _ M (Law707.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 1629 `x = (x ◇ x) ◇ ((x ◇ x) ◇ x)` holds of the right division of any magma satisfying
equation 707 `x = y ◇ (y ◇ ((x ◇ y) ◇ y))` and equipped with two-sided divisions. -/
private theorem aux707_1629R [Finite G] [Magma G] (h : Equation707 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dr (dr x x) (dr (dr x x) x) := by
  by_contra nh
  have ef12 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef20 : x ≠ dr (dr x x) (dr (dr x x) x) := mod_symm nh
  have ef23 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = dr X0 X1 := by
    first | exact superpose ef16 ef12 | exact superpose ef12 ef16
  have ef78 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = dr (dr X0 X1) X1 := by
    first | exact superpose ef16 ef23 | exact superpose ef23 ef16
  have ef94 (X0 X1 : G) : dr (dr X0 X1) (X1 ◇ (X0 ◇ X1)) = X1 := by
    first | exact superpose ef23 ef17 | exact superpose ef17 ef23
  have ef234 : x ≠ dr (dr x x) (x ◇ (x ◇ x)) := by
    first | exact superpose ef78 ef20 | exact superpose ef20 ef78
  subsumption ef234 ef94

theorem Equation1629_termStructuralFromFin_Equation707_finiteDivisionR :
    Law1629.TermStructuralFromFin Law707 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj707R G _ M (Law707.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj707L G _ M (Law707.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1629.models_iff]
    exact fun x ↦
      @aux707_1629R G _ M (Law707.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 1832 `x = (x ◇ (x ◇ x)) ◇ (x ◇ x)` holds of the right division of any magma satisfying
equation 707 `x = y ◇ (y ◇ ((x ◇ y) ◇ y))` and equipped with two-sided divisions. -/
private theorem aux707_1832R [Finite G] [Magma G] (h : Equation707 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dr (dr x (dr x x)) (dr x x) := by
  by_contra nh
  have ef12 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (h ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef20 : x ≠ dr (dr x (dr x x)) (dr x x) := mod_symm nh
  have ef23 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = dr X0 X1 := by
    first | exact superpose ef16 ef12 | exact superpose ef12 ef16
  have ef78 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = dr (dr X0 X1) X1 := by
    first | exact superpose ef16 ef23 | exact superpose ef23 ef16
  have ef232 : x ≠ (dr x x) ◇ ((dr x x) ◇ x) := by
    first | exact superpose ef78 ef20 | exact superpose ef20 ef78
  have ef235 : x ≠ (dr x x) ◇ x := by
    first | exact superpose ef16 ef232 | exact superpose ef232 ef16
  subsumption ef235 ef16

theorem Equation1832_termStructuralFromFin_Equation707_finiteDivisionR :
    Law1832.TermStructuralFromFin Law707 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj707R G _ M (Law707.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj707L G _ M (Law707.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1832.models_iff]
    exact fun x ↦
      @aux707_1832R G _ M (Law707.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

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

theorem Equation464_termStructuralFromFin_Equation714_finiteDivisionL :
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

/-- Left translation by `t` is injective in every finite magma satisfying equation 872
`x = y ◇ ((x ◇ x) ◇ (y ◇ x))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj872L [Finite G] [Magma G] (h : Equation872 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ (z ◇ z) ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef13 : q = ((t ◇ p) ◇ (t ◇ p)) ◇ (t ◇ (t ◇ p)) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef17 : p = q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef17 ef10

/-- Equation 614 `x = x ◇ (x ◇ ((x ◇ x) ◇ x))` holds of the left division of any magma satisfying
equation 872 `x = y ◇ ((x ◇ x) ◇ (y ◇ x))` and equipped with that one division. -/
private theorem aux872_614L1 [Finite G] [Magma G] (h : Equation872 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl x (dl x (dl (dl x x) x)) := by
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ (z ◇ z) ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (h ..)
  have ef9 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef11 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef12 : x ≠ dl x (dl x (dl (dl x x) x)) := mod_symm nh
  have ef15 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X0) = dl X1 X0 := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  have ef36 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = dl ((X1 ◇ X0) ◇ (X1 ◇ X0)) X0 := by
    first | exact superpose ef9 ef11 | exact superpose ef11 ef9
  have ef64 (X0 : G) : X0 ◇ (X0 ◇ X0) = dl (dl X0 X0) X0 := by
    first | exact superpose ef15 ef36 | exact superpose ef36 ef15
  have ef93 : x ≠ dl x (dl x (x ◇ (x ◇ x))) := by
    first | exact superpose ef64 ef12 | exact superpose ef12 ef64
  have ef94 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef11 ef93 | exact superpose ef93 ef11
  subsumption ef94 ef11

theorem Equation614_termStructuralFromFin_Equation872_finiteDivisionL :
    Law614.TermStructuralFromFin Law872 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj872L G _ M (Law872.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law614.models_iff]
    exact fun x ↦
      @aux872_614L1 G _ M (Law872.models_iff.mp hGL) dl h1 h2 x

/-- Left translation by `t` is injective in every finite magma satisfying equation 873
`x = y ◇ ((x ◇ x) ◇ (y ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj873L [Finite G] [Magma G] (h : Equation873 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ (b ◇ b))) ◇ (b ◇ (a ◇ (b ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ hrot0 z b) a
  have ef10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef14 : q = ((t ◇ p) ◇ (t ◇ p)) ◇ (t ◇ t) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef16 : p = q := by
    first | exact superpose ef10 ef14 | exact superpose ef14 ef10
  subsumption ef16 ef12

/-- Right translation by `t` is injective in every finite magma satisfying equation 873
`x = y ◇ ((x ◇ x) ◇ (y ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj873R [Finite G] [Magma G] (h : Equation873 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ (b ◇ b))) ◇ (b ◇ (a ◇ (b ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ z ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ hrot0 z b) a
  have ef10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef11 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef14 : t = ((p ◇ t) ◇ (p ◇ t)) ◇ (q ◇ q) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef15 (X0 X1 : G) :
      X1 ◇ X1 = (X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    first | exact superpose ef10 ef10
  have ef17 : q ◇ q = (t ◇ t) ◇ (((p ◇ t) ◇ (p ◇ t)) ◇ ((p ◇ t) ◇ (p ◇ t))) := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef18 : q ◇ q = p ◇ p := by
    first | exact superpose ef15 ef17 | exact superpose ef17 ef15
  have ef31 : q = ((p ◇ p) ◇ (p ◇ p)) ◇ (p ◇ p) := by
    first | exact superpose ef18 ef10 | exact superpose ef10 ef18
  have ef32 : p = q := by
    first | exact superpose ef10 ef31 | exact superpose ef31 ef10
  subsumption ef32 ef12

/-- Equation 99 `x = x ◇ ((x ◇ x) ◇ x)` holds of the left division of any magma satisfying equation
873 `x = y ◇ ((x ◇ x) ◇ (y ◇ y))` and equipped with two-sided divisions. -/
private theorem aux873_99L [Finite G] [Magma G] (h : Equation873 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl x (dl (dl x x) x) := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : x ≠ dl x (dl (dl x x) x) := mod_symm nh
  have ef22 (X0 X1 : G) : (X0 ◇ X0) ◇ (X1 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef60 (X0 : G) : X0 ◇ X0 = dl ((X0 ◇ X0) ◇ (X0 ◇ X0)) X0 := by
    first | exact superpose ef22 ef11 | exact superpose ef11 ef22
  have ef75 (X0 : G) : X0 ◇ X0 = dl (dl X0 X0) X0 := by
    first | exact superpose ef22 ef60 | exact superpose ef60 ef22
  have ef138 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef75 ef18 | exact superpose ef18 ef75
  subsumption ef138 ef17

theorem Equation99_termStructuralFromFin_Equation873_finiteDivisionL :
    Law99.TermStructuralFromFin Law873 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj873R G _ M (Law873.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj873L G _ M (Law873.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law99.models_iff]
    exact fun x ↦
      @aux873_99L G _ M (Law873.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Left translation by `t` is injective in every finite magma satisfying equation 879
`x = y ◇ ((x ◇ y) ◇ (x ◇ x))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj879L [Finite G] [Magma G] (h : Equation879 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ a) ◇ b) ◇ ((b ◇ a) ◇ (b ◇ a)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ (z ◇ b) ◇ (z ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef13 : q = ((t ◇ p) ◇ t) ◇ ((t ◇ p) ◇ (t ◇ p)) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef16 : p = q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef16 ef10

/-- Equation 614 `x = x ◇ (x ◇ ((x ◇ x) ◇ x))` holds of the left division of any magma satisfying
equation 879 `x = y ◇ ((x ◇ y) ◇ (x ◇ x))` and equipped with that one division. -/
private theorem aux879_614L1 [Finite G] [Magma G] (h : Equation879 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl x (dl x (dl (dl x x) x)) := by
  by_contra nh
  have ef8 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have ef10 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef11 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef12 : x ≠ dl x (dl x (dl (dl x x) x)) := mod_symm nh
  have ef13 (X0 X1 : G) : (dl X1 X0) ◇ (X0 ◇ (X1 ◇ X1)) = X1 := by
    first | exact superpose ef10 ef8 | exact superpose ef8 ef10
  have ef21 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl (dl X0 X1) X0 := by
    first | exact superpose ef13 ef11 | exact superpose ef11 ef13
  have ef96 : x ≠ dl x (dl x (x ◇ (x ◇ x))) := by
    first | exact superpose ef21 ef12 | exact superpose ef12 ef21
  have ef97 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef11 ef96 | exact superpose ef96 ef11
  subsumption ef97 ef11

theorem Equation614_termStructuralFromFin_Equation879_finiteDivisionL :
    Law614.TermStructuralFromFin Law879 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj879L G _ M (Law879.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law614.models_iff]
    exact fun x ↦
      @aux879_614L1 G _ M (Law879.models_iff.mp hGL) dl h1 h2 x

/-- Equation 632 `x = x ◇ (y ◇ ((x ◇ y) ◇ x))` holds of the left division of any magma satisfying
equation 879 `x = y ◇ ((x ◇ y) ◇ (x ◇ x))` and equipped with that one division. -/
private theorem aux879_632L1 [Finite G] [Magma G] (h : Equation879 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl y (dl (dl x y) x)) := by
  by_contra nh
  have ef8 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := mod_symm (h ..)
  have ef10 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef11 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef12 : x ≠ dl x (dl y (dl (dl x y) x)) := mod_symm nh
  have ef13 (X0 X1 : G) : (dl X1 X0) ◇ (X0 ◇ (X1 ◇ X1)) = X1 := by
    first | exact superpose ef10 ef8 | exact superpose ef8 ef10
  have ef21 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl (dl X0 X1) X0 := by
    first | exact superpose ef13 ef11 | exact superpose ef11 ef13
  have ef94 : x ≠ dl x (dl y (y ◇ (x ◇ x))) := by
    first | exact superpose ef21 ef12 | exact superpose ef12 ef21
  have ef97 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef11 ef94 | exact superpose ef94 ef11
  subsumption ef97 ef11

theorem Equation632_termStructuralFromFin_Equation879_finiteDivisionL :
    Law632.TermStructuralFromFin Law879 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj879L G _ M (Law879.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law632.models_iff]
    exact fun x y ↦
      @aux879_632L1 G _ M (Law879.models_iff.mp hGL) dl h1 h2 x y

/-- Left translation by `t` is injective in every finite magma satisfying equation 910
`x = y ◇ ((y ◇ x) ◇ (y ◇ y))`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj910L [Finite G] [Magma G] (h : Equation910 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have ef8 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef13 : q = t ◇ ((t ◇ p) ◇ (t ◇ t)) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef15 : p = q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef15 ef12

/-- Equation 427 `x = x ◇ (y ◇ (x ◇ (x ◇ y)))` holds of the left division of any magma satisfying
equation 910 `x = y ◇ ((y ◇ x) ◇ (y ◇ y))` and equipped with that one division. -/
private theorem aux910_427L1 [Finite G] [Magma G] (h : Equation910 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl x (dl y (dl x (dl x y))) := by
  by_contra nh
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef13 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef14 : x ≠ dl x (dl y (dl x (dl x y))) := mod_symm nh
  have ef15 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef12 ef9 | exact superpose ef9 ef12
  have ef39 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl X0 (dl X0 X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef112 : x ≠ dl x (dl y (y ◇ (x ◇ x))) := by
    first | exact superpose ef39 ef14 | exact superpose ef14 ef39
  have ef113 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef13 ef112 | exact superpose ef112 ef13
  subsumption ef113 ef13

theorem Equation427_termStructuralFromFin_Equation910_finiteDivisionL :
    Law427.TermStructuralFromFin Law910 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj910L G _ M (Law910.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law427.models_iff]
    exact fun x y ↦
      @aux910_427L1 G _ M (Law910.models_iff.mp hGL) dl h1 h2 x y

/-- Equation 1020 `x = x ◇ ((x ◇ (x ◇ x)) ◇ x)` holds of the left division of any magma satisfying
equation 910 `x = y ◇ ((y ◇ x) ◇ (y ◇ y))` and equipped with that one division. -/
private theorem aux910_1020L1 [Finite G] [Magma G] (h : Equation910 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl x (dl (dl x (dl x x)) x) := by
  by_contra nh
  have hrot0 (a b : G) : b ◇ (b ◇ (a ◇ (b ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (b ◇ b))) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : (b ◇ (b ◇ a)) ◇ (b ◇ b) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (b ◇ z)) (g := fun z ↦ z ◇ (b ◇ b))
      (fun z ↦ hrot0 z b) a
  have ef9 (X0 X1 : G) : X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef12 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef13 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef14 : x ≠ dl x (dl (dl x (dl x x)) x) := mod_symm nh
  have ef15 (X0 X1 : G) : X1 ◇ (X0 ◇ (X1 ◇ X1)) = dl X1 X0 := by
    first | exact superpose ef12 ef9 | exact superpose ef9 ef12
  have ef25 (X0 X1 : G) : X1 ◇ X1 = dl (X1 ◇ (X1 ◇ X0)) X0 := by
    first | exact superpose ef11 ef13 | exact superpose ef13 ef11
  have ef39 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl X0 (dl X0 X1) := by
    first | exact superpose ef15 ef13 | exact superpose ef13 ef15
  have ef112 : x ≠ dl x (dl (x ◇ (x ◇ x)) x) := by
    first | exact superpose ef39 ef14 | exact superpose ef14 ef39
  have ef113 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef25 ef112 | exact superpose ef112 ef25
  subsumption ef113 ef13

theorem Equation1020_termStructuralFromFin_Equation910_finiteDivisionL :
    Law1020.TermStructuralFromFin Law910 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj910L G _ M (Law910.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law1020.models_iff]
    exact fun x ↦
      @aux910_1020L1 G _ M (Law910.models_iff.mp hGL) dl h1 h2 x

/-- Left translation by `t` is injective in every finite magma satisfying equation 1083
`x = y ◇ ((x ◇ (y ◇ x)) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1083L [Finite G] [Magma G] (h : Equation1083 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ a) ◇ (b ◇ (b ◇ a))) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ (b ◇ (b ◇ z))) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef10 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef16 : q = ((t ◇ p) ◇ (t ◇ (t ◇ p))) ◇ t := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef19 : p = q := by
    first | exact superpose ef10 ef16 | exact superpose ef16 ef10
  subsumption ef19 ef12

/-- Right translation by `t` is injective in every finite magma satisfying equation 1083
`x = y ◇ ((x ◇ (y ◇ x)) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1083R [Finite G] [Magma G] (h : Equation1083 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (a ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ z ◇ (b ◇ z))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have ef9 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := mod_symm (hrot0 ..)
  have ef11 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef13 : t = q ◇ ((t ◇ (p ◇ t)) ◇ q) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef19 : q = (t ◇ (p ◇ t)) ◇ (t ◇ (t ◇ (p ◇ t))) := by
    first | exact superpose ef13 ef8 | exact superpose ef8 ef13
  have ef22 : p = q := by
    first | exact superpose ef9 ef19 | exact superpose ef19 ef9
  subsumption ef22 ef12

/-- Equation 203 `x = (x ◇ (x ◇ x)) ◇ x` holds of the right division of any magma satisfying
equation 1083 `x = y ◇ ((x ◇ (y ◇ x)) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux1083_203R [Finite G] [Magma G] (h : Equation1083 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dr (dr x (dr x x)) x := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : x ≠ dr (dr x (dr x x)) x := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef20 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef14 ef17 | exact superpose ef17 ef14
  have ef25 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) ◇ X1 = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef69 (X0 X1 : G) : dl (X1 ◇ (X0 ◇ X1)) (dl X0 X1) = X0 := by
    first | exact superpose ef25 ef17 | exact superpose ef17 ef25
  have ef95 (X0 X1 : G) : dr X0 X1 = dl (X1 ◇ X0) (dl (dr X0 X1) X1) := by
    first | exact superpose ef14 ef69 | exact superpose ef69 ef14
  have ef832 (X0 : G) : dr X0 X0 = dl (X0 ◇ X0) X0 := by
    first | exact superpose ef20 ef95 | exact superpose ef95 ef20
  have ef926 (X0 : G) : X0 ◇ X0 = dr X0 (dr X0 X0) := by
    first | exact superpose ef832 ef19 | exact superpose ef19 ef832
  have ef1043 : x ≠ dr (x ◇ x) x := by
    first | exact superpose ef926 ef18 | exact superpose ef18 ef926
  subsumption ef1043 ef15

theorem Equation203_termStructuralFromFin_Equation1083_finiteDivisionR :
    Law203.TermStructuralFromFin Law1083 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1083R G _ M (Law1083.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1083L G _ M (Law1083.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law203.models_iff]
    exact fun x ↦
      @aux1083_203R G _ M (Law1083.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Left translation by `t` is injective in every finite magma satisfying equation 1117
`x = y ◇ ((y ◇ (x ◇ z)) ◇ z)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1117L [Finite G] [Magma G] (h : Equation1117 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ ((b ◇ a) ◇ c)) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((b ◇ z) ◇ c)) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have ef8 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef13 (X0 : G) : q = (t ◇ ((t ◇ p) ◇ X0)) ◇ X0 := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef19 : p = q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef19 ef10

/-- Right translation by `t` is injective in every finite magma satisfying equation 1117
`x = y ◇ ((y ◇ (x ◇ z)) ◇ z)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1117R [Finite G] [Magma G] (h : Equation1117 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have ef7 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have ef9 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 (X0 : G) : q = X0 ◇ ((X0 ◇ (p ◇ t)) ◇ t) := by
    first | exact superpose ef9 ef7 | exact superpose ef7 ef9
  have ef13 : p = q := by
    first | exact superpose ef7 ef11 | exact superpose ef11 ef7
  subsumption ef13 ef10

/-- Equation 4290 `x ◇ (x ◇ y) = y ◇ (x ◇ x)` holds of the left division of any magma satisfying
equation 1117 `x = y ◇ ((y ◇ (x ◇ z)) ◇ z)` and equipped with two-sided divisions. -/
private theorem aux1117_4290L [Finite G] [Magma G] (h : Equation1117 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dl x (dl x y) = dl y (dl x x) := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dl x (dl x y) ≠ dl y (dl x x) := mod_symm nh
  have ef20 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ X0) ◇ (dl X2 X0)) = X2 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef72 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (dl X2 (dl X1 X0))) = X2 := by
    first | exact superpose ef14 ef20 | exact superpose ef20 ef14
  have ef425 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ (dl X0 (dl X1 X2)) := by
    first | exact superpose ef72 ef15 | exact superpose ef15 ef72
  have ef2397 (X0 X1 X2 : G) : dl X2 (dl X0 X1) = dl X1 (dl X0 X2) := by
    first | exact superpose ef425 ef15 | exact superpose ef15 ef425
  have ef5492 : dl x (dl x y) ≠ dl x (dl x y) := by
    first | exact superpose ef2397 ef16 | exact superpose ef16 ef2397
  exact absurd rfl ef5492

theorem Equation4290_termStructuralFromFin_Equation1117_finiteDivisionL :
    Law4290.TermStructuralFromFin Law1117 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1117R G _ M (Law1117.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1117L G _ M (Law1117.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4290.models_iff]
    exact fun x y ↦
      @aux1117_4290L G _ M (Law1117.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4369 `x ◇ (y ◇ z) = z ◇ (y ◇ x)` holds of the left division of any magma satisfying
equation 1117 `x = y ◇ ((y ◇ (x ◇ z)) ◇ z)` and equipped with two-sided divisions. -/
private theorem aux1117_4369L [Finite G] [Magma G] (h : Equation1117 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    dl x (dl y z) = dl z (dl y x) := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dl x (dl y z) ≠ dl z (dl y x) := mod_symm nh
  have ef20 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ X0) ◇ (dl X2 X0)) = X2 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef72 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (dl X2 (dl X1 X0))) = X2 := by
    first | exact superpose ef14 ef20 | exact superpose ef20 ef14
  have ef425 (X0 X1 X2 : G) : dl X1 X0 = X2 ◇ (dl X0 (dl X1 X2)) := by
    first | exact superpose ef72 ef15 | exact superpose ef15 ef72
  have ef2397 (X0 X1 X2 : G) : dl X2 (dl X0 X1) = dl X1 (dl X0 X2) := by
    first | exact superpose ef425 ef15 | exact superpose ef15 ef425
  have ef5492 : dl x (dl y z) ≠ dl x (dl y z) := by
    first | exact superpose ef2397 ef16 | exact superpose ef16 ef2397
  exact absurd rfl ef5492

theorem Equation4369_termStructuralFromFin_Equation1117_finiteDivisionL :
    Law4369.TermStructuralFromFin Law1117 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1117R G _ M (Law1117.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1117L G _ M (Law1117.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4369.models_iff]
    exact fun x y z ↦
      @aux1117_4369L G _ M (Law1117.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

/-- Equation 4605 `(x ◇ x) ◇ y = (y ◇ x) ◇ x` holds of the right division of any magma satisfying
equation 1117 `x = y ◇ ((y ◇ (x ◇ z)) ◇ z)` and equipped with two-sided divisions. -/
private theorem aux1117_4605R [Finite G] [Magma G] (h : Equation1117 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr (dr x x) y = dr (dr y x) x := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 : dr (dr x x) y ≠ dr (dr y x) x := mod_symm nh
  have ef19 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ X0) ◇ X2) = dr X0 X2 := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef48 (X0 X1 X2 : G) : dr X1 X2 = (dr X0 X1) ◇ (X0 ◇ X2) := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef247 (X0 X1 X2 : G) : dr X1 X2 = (dr (dr X0 X2) X1) ◇ X0 := by
    first | exact superpose ef12 ef48 | exact superpose ef48 ef12
  have ef1470 (X0 X1 X2 : G) : dr (dr X0 X1) X2 = dr (dr X2 X1) X0 := by
    first | exact superpose ef247 ef13 | exact superpose ef13 ef247
  have ef4910 : dr (dr x x) y ≠ dr (dr x x) y := by
    first | exact superpose ef1470 ef16 | exact superpose ef16 ef1470
  exact absurd rfl ef4910

theorem Equation4605_termStructuralFromFin_Equation1117_finiteDivisionR :
    Law4605.TermStructuralFromFin Law1117 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1117R G _ M (Law1117.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1117L G _ M (Law1117.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4605.models_iff]
    exact fun x y ↦
      @aux1117_4605R G _ M (Law1117.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4684 `(x ◇ y) ◇ z = (z ◇ y) ◇ x` holds of the right division of any magma satisfying
equation 1117 `x = y ◇ ((y ◇ (x ◇ z)) ◇ z)` and equipped with two-sided divisions. -/
private theorem aux1117_4684R [Finite G] [Magma G] (h : Equation1117 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y z : G) :
    dr (dr x y) z = dr (dr z y) x := by
  by_contra nh
  have ef10 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 : dr (dr x y) z ≠ dr (dr z y) x := mod_symm nh
  have ef19 (X0 X1 X2 : G) : X1 ◇ ((X1 ◇ X0) ◇ X2) = dr X0 X2 := by
    first | exact superpose ef12 ef10 | exact superpose ef10 ef12
  have ef48 (X0 X1 X2 : G) : dr X1 X2 = (dr X0 X1) ◇ (X0 ◇ X2) := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef247 (X0 X1 X2 : G) : dr X1 X2 = (dr (dr X0 X2) X1) ◇ X0 := by
    first | exact superpose ef12 ef48 | exact superpose ef48 ef12
  have ef1470 (X0 X1 X2 : G) : dr (dr X0 X1) X2 = dr (dr X2 X1) X0 := by
    first | exact superpose ef247 ef13 | exact superpose ef13 ef247
  have ef4885 : dr (dr x y) z ≠ dr (dr x y) z := by
    first | exact superpose ef1470 ef16 | exact superpose ef16 ef1470
  exact absurd rfl ef4885

theorem Equation4684_termStructuralFromFin_Equation1117_finiteDivisionR :
    Law4684.TermStructuralFromFin Law1117 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1117R G _ M (Law1117.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1117L G _ M (Law1117.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4684.models_iff]
    exact fun x y z ↦
      @aux1117_4684R G _ M (Law1117.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y z

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

theorem Equation2847_termStructuralFromFin_Equation1276_finiteDivisionR :
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

theorem Equation2909_termStructuralFromFin_Equation1276_finiteDivisionR :
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

theorem Equation4273_termStructuralFromFin_Equation1276_finiteDivisionR :
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

/-- Left translation by `t` is injective in every finite magma satisfying equation 1285
`x = y ◇ (((x ◇ y) ◇ x) ◇ x)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1285L [Finite G] [Magma G] (h : Equation1285 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (((b ◇ a) ◇ b) ◇ (b ◇ a)) ◇ (b ◇ a) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ ((z ◇ b) ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef13 : q = (((t ◇ p) ◇ t) ◇ (t ◇ p)) ◇ (t ◇ p) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef16 : p = q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef16 ef10

/-- Equation 2035 `x = ((x ◇ x) ◇ x) ◇ (x ◇ x)` holds of the left division of any magma satisfying
equation 1285 `x = y ◇ (((x ◇ y) ◇ x) ◇ x)` and equipped with that one division. -/
private theorem aux1285_2035L1 [Finite G] [Magma G] (h : Equation1285 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl (dl (dl x x) x) (dl x x) := by
  by_contra nh
  have ef8 (X0 X1 : G) : X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := mod_symm (h ..)
  have ef10 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef11 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef12 : x ≠ dl (dl (dl x x) x) (dl x x) := mod_symm nh
  have ef13 (X0 X1 : G) : (dl X1 X0) ◇ ((X0 ◇ X1) ◇ X1) = X1 := by
    first | exact superpose ef10 ef8 | exact superpose ef8 ef10
  have ef15 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) ◇ X0 = dl X1 X0 := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  have ef22 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = dl (dl X0 X1) X0 := by
    first | exact superpose ef13 ef11 | exact superpose ef11 ef13
  have ef48 (X0 X1 : G) : dl ((X1 ◇ X0) ◇ X1) (dl X0 X1) = X1 := by
    first | exact superpose ef15 ef11 | exact superpose ef11 ef15
  have ef67 : x ≠ dl ((x ◇ x) ◇ x) (dl x x) := by
    first | exact superpose ef22 ef12 | exact superpose ef12 ef22
  subsumption ef67 ef48

theorem Equation2035_termStructuralFromFin_Equation1285_finiteDivisionL :
    Law2035.TermStructuralFromFin Law1285 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj1285L G _ M (Law1285.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law2035.models_iff]
    exact fun x ↦
      @aux1285_2035L1 G _ M (Law1285.models_iff.mp hGL) dl h1 h2 x

/-- Left translation by `t` is injective in every finite magma satisfying equation 1286
`x = y ◇ (((x ◇ y) ◇ x) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1286L [Finite G] [Magma G] (h : Equation1286 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ (a ◇ b)) ◇ b) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ (z ◇ b) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : (((b ◇ a) ◇ b) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ ((b ◇ z) ◇ b) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef10 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef15 : q = (((t ◇ p) ◇ t) ◇ (t ◇ p)) ◇ t := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef18 : p = q := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  subsumption ef18 ef12

/-- Right translation by `t` is injective in every finite magma satisfying equation 1286
`x = y ◇ (((x ◇ y) ◇ x) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1286R [Finite G] [Magma G] (h : Equation1286 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : ((b ◇ (a ◇ b)) ◇ b) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ (z ◇ b) ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef9 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef11 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef24 : q = ((t ◇ (p ◇ t)) ◇ t) ◇ (t ◇ (p ◇ t)) := by
    first | exact superpose ef11 ef9 | exact superpose ef9 ef11
  have ef29 : p = q := by
    first | exact superpose ef9 ef24 | exact superpose ef24 ef9
  subsumption ef29 ef12

/-- Equation 1426 `x = (x ◇ x) ◇ (x ◇ (x ◇ x))` holds of the right division of any magma satisfying
equation 1286 `x = y ◇ (((x ◇ y) ◇ x) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux1286_1426R [Finite G] [Magma G] (h : Equation1286 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dr (dr x x) (dr x (dr x x)) := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : x ≠ dr (dr x x) (dr x (dr x x)) := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef20 (X0 X1 : G) : dl (dr X0 X1) X0 = X1 := by
    first | exact superpose ef14 ef17 | exact superpose ef17 ef14
  have ef24 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) ◇ X1 = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef55 (X0 X1 : G) : (X0 ◇ (dr X0 X1)) ◇ X1 = dl X1 (dr X0 X1) := by
    first | exact superpose ef14 ef24 | exact superpose ef24 ef14
  have ef68 (X0 X1 : G) : dl ((X1 ◇ X0) ◇ X1) (dl X0 X1) = X0 := by
    first | exact superpose ef24 ef17 | exact superpose ef17 ef24
  have ef69 (X0 X1 : G) : (X1 ◇ X0) ◇ X1 = dr (dl X0 X1) X0 := by
    first | exact superpose ef24 ef15 | exact superpose ef15 ef24
  have ef140 (X0 X1 : G) : (X1 ◇ (dr X1 X0)) ◇ X1 = dr X0 (dr X1 X0) := by
    first | exact superpose ef20 ef69 | exact superpose ef69 ef20
  have ef347 (X0 : G) : dr X0 X0 = dl (dl X0 (dr X0 X0)) (dl (dr X0 X0) X0) := by
    first | exact superpose ef55 ef68 | exact superpose ef68 ef55
  have ef370 (X0 : G) : dr X0 X0 = dl (dl X0 (dr X0 X0)) X0 := by
    first | exact superpose ef20 ef347 | exact superpose ef347 ef20
  have ef451 (X0 : G) : dl X0 (dr X0 X0) = dr X0 (dr X0 X0) := by
    first | exact superpose ef370 ef19 | exact superpose ef19 ef370
  have ef649 (X0 : G) : dr X0 X0 = X0 ◇ (dr X0 (dr X0 X0)) := by
    first | exact superpose ef451 ef16 | exact superpose ef16 ef451
  have ef1422 : x ≠ (x ◇ (dr x (dr x x))) ◇ x := by
    first | exact superpose ef140 ef18 | exact superpose ef18 ef140
  have ef1423 : x ≠ (dr x x) ◇ x := by
    first | exact superpose ef649 ef1422 | exact superpose ef1422 ef649
  subsumption ef1423 ef14

theorem Equation1426_termStructuralFromFin_Equation1286_finiteDivisionR :
    Law1426.TermStructuralFromFin Law1286 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1286R G _ M (Law1286.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1286L G _ M (Law1286.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1426.models_iff]
    exact fun x ↦
      @aux1286_1426R G _ M (Law1286.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Left translation by `t` is injective in every finite magma satisfying equation 1288
`x = y ◇ (((x ◇ y) ◇ y) ◇ x)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1288L [Finite G] [Magma G] (h : Equation1288 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (((b ◇ a) ◇ b) ◇ b) ◇ (b ◇ a) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ ((z ◇ b) ◇ b) ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) ◇ (X1 ◇ X0) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef13 : q = (((t ◇ p) ◇ t) ◇ t) ◇ (t ◇ p) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef16 : p = q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef16 ef10

/-- Equation 99 `x = x ◇ ((x ◇ x) ◇ x)` holds of the left division of any magma satisfying equation
1288 `x = y ◇ (((x ◇ y) ◇ y) ◇ x)` and equipped with that one division. -/
private theorem aux1288_99L1 [Finite G] [Magma G] (h : Equation1288 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl x (dl (dl x x) x) := by
  by_contra nh
  have ef8 (X0 X1 : G) : X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have ef11 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef12 : x ≠ dl x (dl (dl x x) x) := mod_symm nh
  have ef15 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) ◇ X0 = dl X1 X0 := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  have ef20 (X0 : G) : dl X0 (X0 ◇ X0) = (dl X0 X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef15 ef15
  have ef25 (X0 : G) : (dl X0 X0) ◇ (X0 ◇ X0) = X0 := by
    first | exact superpose ef11 ef20 | exact superpose ef20 ef11
  have ef41 (X0 : G) : X0 ◇ X0 = dl (dl X0 X0) X0 := by
    first | exact superpose ef25 ef11 | exact superpose ef11 ef25
  have ef54 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef41 ef12 | exact superpose ef12 ef41
  subsumption ef54 ef11

theorem Equation99_termStructuralFromFin_Equation1288_finiteDivisionL :
    Law99.TermStructuralFromFin Law1288 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj1288L G _ M (Law1288.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law99.models_iff]
    exact fun x ↦
      @aux1288_99L1 G _ M (Law1288.models_iff.mp hGL) dl h1 h2 x

/-- Left translation by `t` is injective in every finite magma satisfying equation 1313
`x = y ◇ (((y ◇ x) ◇ x) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1313L [Finite G] [Magma G] (h : Equation1313 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (a ◇ b))) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ (b ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ (b ◇ a)) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef10 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef15 : q = ((t ◇ (t ◇ p)) ◇ (t ◇ p)) ◇ t := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef18 : p = q := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  subsumption ef18 ef12

/-- Right translation by `t` is injective in every finite magma satisfying equation 1313
`x = y ◇ (((y ◇ x) ◇ x) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1313R [Finite G] [Magma G] (h : Equation1313 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (a ◇ b))) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ (b ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef9 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef11 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef20 : q = (t ◇ (t ◇ (p ◇ t))) ◇ (t ◇ (p ◇ t)) := by
    first | exact superpose ef11 ef9 | exact superpose ef9 ef11
  have ef27 : p = q := by
    first | exact superpose ef9 ef20 | exact superpose ef20 ef9
  subsumption ef27 ef12

/-- Equation 2847 `x = ((x ◇ (x ◇ x)) ◇ x) ◇ x` holds of the left division of any magma satisfying
equation 1313 `x = y ◇ (((y ◇ x) ◇ x) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux1313_2847L [Finite G] [Magma G] (h : Equation1313 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl (dl (dl x (dl x x)) x) x := by
  by_contra nh
  have ef11 (X0 X1 : G) : X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : x ≠ dl (dl (dl x (dl x x)) x) x := mod_symm nh
  have ef22 (X0 X1 : G) : dl X1 X0 = X1 ◇ ((X0 ◇ (dl X1 X0)) ◇ X1) := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef24 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) ◇ X1 = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef61 (X0 : G) : dl (X0 ◇ X0) X0 = (dl X0 X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef24 ef24
  have ef69 (X0 X1 : G) : dl ((X0 ◇ X1) ◇ X1) (dl X0 X1) = X0 := by
    first | exact superpose ef24 ef17 | exact superpose ef17 ef24
  have ef184 (X0 : G) : dl X0 X0 = X0 ◇ (X0 ◇ X0) := by
    first | exact superpose ef16 ef22 | exact superpose ef22 ef16
  have ef214 (X0 : G) : X0 ◇ X0 = dl X0 (dl X0 X0) := by
    first | exact superpose ef184 ef17 | exact superpose ef17 ef184
  have ef218 (X0 : G) : dl ((dl X0 X0) ◇ (X0 ◇ X0)) (dl X0 (X0 ◇ X0)) = X0 := by
    first | exact superpose ef184 ef69 | exact superpose ef69 ef184
  have ef221 (X0 : G) : dl ((dl X0 X0) ◇ (X0 ◇ X0)) X0 = X0 := by
    first | exact superpose ef17 ef218 | exact superpose ef218 ef17
  have ef229 (X0 : G) : dl (dl (X0 ◇ X0) X0) X0 = X0 := by
    first | exact superpose ef61 ef221 | exact superpose ef221 ef61
  have ef311 : x ≠ dl (dl (x ◇ x) x) x := by
    first | exact superpose ef214 ef18 | exact superpose ef18 ef214
  subsumption ef311 ef229

theorem Equation2847_termStructuralFromFin_Equation1313_finiteDivisionL :
    Law2847.TermStructuralFromFin Law1313 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1313R G _ M (Law1313.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1313L G _ M (Law1313.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law2847.models_iff]
    exact fun x ↦
      @aux1313_2847L G _ M (Law1313.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 203 `x = (x ◇ (x ◇ x)) ◇ x` holds of the right division of any magma satisfying
equation 1313 `x = y ◇ (((y ◇ x) ◇ x) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux1313_203R [Finite G] [Magma G] (h : Equation1313 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dr (dr x (dr x x)) x := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ (b ◇ (a ◇ b))) ◇ (b ◇ (a ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ b)) (g := fun z ↦ (b ◇ z) ◇ z)
      (fun z ↦ (h z b).symm) a
  have hrot1 (a b : G) : ((b ◇ (b ◇ a)) ◇ (b ◇ a)) ◇ b = a :=
    rot_of_finite (f := fun z ↦ (b ◇ (b ◇ z)) ◇ (b ◇ z)) (g := fun z ↦ z ◇ b)
      (fun z ↦ hrot0 z b) a
  have ef11 (X0 X1 : G) : X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X1 = X0 := mod_symm (hrot1 ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 : x ≠ dr (dr x (dr x x)) x := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef22 (X0 X1 : G) : dl X1 X0 = X1 ◇ ((X0 ◇ (dl X1 X0)) ◇ X1) := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef24 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) ◇ X1 = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef61 (X0 : G) : dl (X0 ◇ X0) X0 = (dl X0 X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef24 ef24
  have ef184 (X0 : G) : dl X0 X0 = X0 ◇ (X0 ◇ X0) := by
    first | exact superpose ef16 ef22 | exact superpose ef22 ef16
  have ef208 (X0 : G) : ((dl X0 X0) ◇ (X0 ◇ X0)) ◇ X0 = X0 := by
    first | exact superpose ef184 ef13 | exact superpose ef13 ef184
  have ef228 (X0 : G) : (dl (X0 ◇ X0) X0) ◇ X0 = X0 := by
    first | exact superpose ef61 ef208 | exact superpose ef208 ef61
  have ef370 (X0 : G) : dl (X0 ◇ X0) X0 = dr X0 X0 := by
    first | exact superpose ef228 ef15 | exact superpose ef15 ef228
  have ef544 (X0 : G) : X0 ◇ X0 = dr X0 (dr X0 X0) := by
    first | exact superpose ef370 ef19 | exact superpose ef19 ef370
  have ef590 : x ≠ dr (x ◇ x) x := by
    first | exact superpose ef544 ef18 | exact superpose ef18 ef544
  subsumption ef590 ef15

theorem Equation203_termStructuralFromFin_Equation1313_finiteDivisionR :
    Law203.TermStructuralFromFin Law1313 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1313R G _ M (Law1313.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1313L G _ M (Law1313.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law203.models_iff]
    exact fun x ↦
      @aux1313_203R G _ M (Law1313.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Left translation by `t` is injective in every finite magma satisfying equation 1316
`x = y ◇ (((y ◇ x) ◇ y) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1316L [Finite G] [Magma G] (h : Equation1316 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have ef9 (X0 X1 : G) : X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef13 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef14 : p ≠ q := mod_symm nh
  have ef15 : q = t ◇ (((t ◇ p) ◇ t) ◇ t) := by
    first | exact superpose ef13 ef9 | exact superpose ef9 ef13
  have ef17 : p = q := by
    first | exact superpose ef9 ef15 | exact superpose ef15 ef9
  subsumption ef17 ef14

/-- Right translation by `t` is injective in every finite magma satisfying equation 1316
`x = y ◇ (((y ◇ x) ◇ y) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1316R [Finite G] [Magma G] (h : Equation1316 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : b ◇ (b ◇ ((a ◇ b) ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((z ◇ b) ◇ b)) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef10 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef13 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef14 : p ≠ q := mod_symm nh
  have ef17 : q = t ◇ (t ◇ ((p ◇ t) ◇ t)) := by
    first | exact superpose ef13 ef10 | exact superpose ef10 ef13
  have ef21 : p = q := by
    first | exact superpose ef10 ef17 | exact superpose ef17 ef10
  subsumption ef21 ef14

/-- Equation 1629 `x = (x ◇ x) ◇ ((x ◇ x) ◇ x)` holds of the left division of any magma satisfying
equation 1316 `x = y ◇ (((y ◇ x) ◇ y) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux1316_1629L [Finite G] [Magma G] (h : Equation1316 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl (dl x x) (dl (dl x x) x) := by
  by_contra nh
  have ef12 (X0 X1 : G) : X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 : x ≠ dl (dl x x) (dl (dl x x) x) := mod_symm nh
  have ef24 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ X1) = dl X1 X0 := by
    first | exact superpose ef18 ef12 | exact superpose ef12 ef18
  have ef93 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = dl X0 (dl X0 X1) := by
    first | exact superpose ef24 ef19 | exact superpose ef19 ef24
  have ef342 : x ≠ (x ◇ (dl x x)) ◇ (dl x x) := by
    first | exact superpose ef93 ef20 | exact superpose ef20 ef93
  have ef350 : x ≠ x ◇ (dl x x) := by
    first | exact superpose ef18 ef342 | exact superpose ef342 ef18
  subsumption ef350 ef18

theorem Equation1629_termStructuralFromFin_Equation1316_finiteDivisionL :
    Law1629.TermStructuralFromFin Law1316 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1316R G _ M (Law1316.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1316L G _ M (Law1316.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1629.models_iff]
    exact fun x ↦
      @aux1316_1629L G _ M (Law1316.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 1832 `x = (x ◇ (x ◇ x)) ◇ (x ◇ x)` holds of the left division of any magma satisfying
equation 1316 `x = y ◇ (((y ◇ x) ◇ y) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux1316_1832L [Finite G] [Magma G] (h : Equation1316 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl (dl x (dl x x)) (dl x x) := by
  by_contra nh
  have ef12 (X0 X1 : G) : X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef18 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef19 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef20 : x ≠ dl (dl x (dl x x)) (dl x x) := mod_symm nh
  have ef24 (X0 X1 : G) : X1 ◇ ((X0 ◇ X1) ◇ X1) = dl X1 X0 := by
    first | exact superpose ef18 ef12 | exact superpose ef12 ef18
  have ef26 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) ◇ X1 = dl X1 X0 := by
    first | exact superpose ef12 ef19 | exact superpose ef19 ef12
  have ef93 (X0 X1 : G) : (X1 ◇ X0) ◇ X0 = dl X0 (dl X0 X1) := by
    first | exact superpose ef24 ef19 | exact superpose ef19 ef24
  have ef120 (X0 X1 : G) : dl ((X0 ◇ X1) ◇ X0) (dl X0 X1) = X0 := by
    first | exact superpose ef26 ef19 | exact superpose ef19 ef26
  have ef347 : x ≠ dl ((x ◇ x) ◇ x) (dl x x) := by
    first | exact superpose ef93 ef20 | exact superpose ef20 ef93
  subsumption ef347 ef120

theorem Equation1832_termStructuralFromFin_Equation1316_finiteDivisionL :
    Law1832.TermStructuralFromFin Law1316 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1316R G _ M (Law1316.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1316L G _ M (Law1316.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1832.models_iff]
    exact fun x ↦
      @aux1316_1832L G _ M (Law1316.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 1629 `x = (x ◇ x) ◇ ((x ◇ x) ◇ x)` holds of the right division of any magma satisfying
equation 1316 `x = y ◇ (((y ◇ x) ◇ y) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux1316_1629R [Finite G] [Magma G] (h : Equation1316 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dr (dr x x) (dr (dr x x) x) := by
  by_contra nh
  have hrot0 (a b : G) : b ◇ (b ◇ ((a ◇ b) ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((z ◇ b) ◇ b)) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef13 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef17 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef20 : x ≠ dr (dr x x) (dr (dr x x) x) := mod_symm nh
  have ef32 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = dr X0 X1 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef150 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = dr (dr X0 X1) X1 := by
    first | exact superpose ef16 ef32 | exact superpose ef32 ef16
  have ef169 (X0 X1 : G) : dr (dr X0 X1) (X1 ◇ (X0 ◇ X1)) = X1 := by
    first | exact superpose ef32 ef17 | exact superpose ef17 ef32
  have ef415 : x ≠ dr (dr x x) (x ◇ (x ◇ x)) := by
    first | exact superpose ef150 ef20 | exact superpose ef20 ef150
  subsumption ef415 ef169

theorem Equation1629_termStructuralFromFin_Equation1316_finiteDivisionR :
    Law1629.TermStructuralFromFin Law1316 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1316R G _ M (Law1316.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1316L G _ M (Law1316.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1629.models_iff]
    exact fun x ↦
      @aux1316_1629R G _ M (Law1316.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Equation 1832 `x = (x ◇ (x ◇ x)) ◇ (x ◇ x)` holds of the right division of any magma satisfying
equation 1316 `x = y ◇ (((y ◇ x) ◇ y) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux1316_1832R [Finite G] [Magma G] (h : Equation1316 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dr (dr x (dr x x)) (dr x x) := by
  by_contra nh
  have hrot0 (a b : G) : b ◇ (b ◇ ((a ◇ b) ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ ((z ◇ b) ◇ b)) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef13 (X0 X1 : G) : X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef16 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef20 : x ≠ dr (dr x (dr x x)) (dr x x) := mod_symm nh
  have ef32 (X0 X1 : G) : X1 ◇ (X1 ◇ (X0 ◇ X1)) = dr X0 X1 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef150 (X0 X1 : G) : X1 ◇ (X1 ◇ X0) = dr (dr X0 X1) X1 := by
    first | exact superpose ef16 ef32 | exact superpose ef32 ef16
  have ef412 : x ≠ (dr x x) ◇ ((dr x x) ◇ x) := by
    first | exact superpose ef150 ef20 | exact superpose ef20 ef150
  have ef417 : x ≠ (dr x x) ◇ x := by
    first | exact superpose ef16 ef412 | exact superpose ef412 ef16
  subsumption ef417 ef16

theorem Equation1832_termStructuralFromFin_Equation1316_finiteDivisionR :
    Law1832.TermStructuralFromFin Law1316 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1316R G _ M (Law1316.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1316L G _ M (Law1316.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law1832.models_iff]
    exact fun x ↦
      @aux1316_1832R G _ M (Law1316.models_iff.mp hGL) dr dl h1 h2 h3 h4 x

/-- Left translation by `t` is injective in every finite magma satisfying equation 1370
`x = y ◇ (((z ◇ y) ◇ y) ◇ x)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1370L [Finite G] [Magma G] (h : Equation1370 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b c : G) : ((c ◇ b) ◇ b) ◇ (b ◇ a) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ ((c ◇ b) ◇ b) ◇ z)
      (fun z ↦ (h z b c).symm) a
  have ef8 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ X0) = X0 := mod_symm (hrot0 ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef17 (X0 : G) : q = ((X0 ◇ t) ◇ t) ◇ (t ◇ p) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef21 : p = q := by
    first | exact superpose ef8 ef17 | exact superpose ef17 ef8
  subsumption ef21 ef10

/-- Equation 99 `x = x ◇ ((x ◇ x) ◇ x)` holds of the left division of any magma satisfying equation
1370 `x = y ◇ (((z ◇ y) ◇ y) ◇ x)` and equipped with that one division. -/
private theorem aux1370_99L1 [Finite G] [Magma G] (h : Equation1370 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl x (dl (dl x x) x) := by
  by_contra nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have ef10 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef11 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef12 : x ≠ dl x (dl (dl x x) x) := mod_symm nh
  have ef15 (X0 X1 X2 : G) : X1 ◇ X0 = dl ((X2 ◇ X1) ◇ X1) X0 := by
    first | exact superpose ef10 ef8 | exact superpose ef8 ef10
  have ef17 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) ◇ X0 = dl X1 X0 := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  have ef44 (X0 X1 : G) : X0 ◇ X1 = dl (dl X0 X0) X1 := by
    first | exact superpose ef17 ef15 | exact superpose ef15 ef17
  have ef132 : x ≠ dl x (x ◇ x) := by
    first | exact superpose ef44 ef12 | exact superpose ef12 ef44
  subsumption ef132 ef11

theorem Equation99_termStructuralFromFin_Equation1370_finiteDivisionL :
    Law99.TermStructuralFromFin Law1370 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj1370L G _ M (Law1370.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law99.models_iff]
    exact fun x ↦
      @aux1370_99L1 G _ M (Law1370.models_iff.mp hGL) dl h1 h2 x

/-- Equation 127 `x = y ◇ ((y ◇ y) ◇ x)` holds of the left division of any magma satisfying equation
1370 `x = y ◇ (((z ◇ y) ◇ y) ◇ x)` and equipped with that one division. -/
private theorem aux1370_127L1 [Finite G] [Magma G] (h : Equation1370 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dl y (dl (dl y y) x) := by
  by_contra nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have ef10 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef11 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef12 : x ≠ dl y (dl (dl y y) x) := mod_symm nh
  have ef15 (X0 X1 X2 : G) : X1 ◇ X0 = dl ((X2 ◇ X1) ◇ X1) X0 := by
    first | exact superpose ef10 ef8 | exact superpose ef8 ef10
  have ef17 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) ◇ X0 = dl X1 X0 := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  have ef44 (X0 X1 : G) : X0 ◇ X1 = dl (dl X0 X0) X1 := by
    first | exact superpose ef17 ef15 | exact superpose ef15 ef17
  have ef127 : x ≠ dl y (y ◇ x) := by
    first | exact superpose ef44 ef12 | exact superpose ef12 ef44
  subsumption ef127 ef11

theorem Equation127_termStructuralFromFin_Equation1370_finiteDivisionL :
    Law127.TermStructuralFromFin Law1370 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj1370L G _ M (Law1370.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law127.models_iff]
    exact fun x y ↦
      @aux1370_127L1 G _ M (Law1370.models_iff.mp hGL) dl h1 h2 x y

/-- Equation 151 `x = (x ◇ x) ◇ (x ◇ x)` holds of the left division of any magma satisfying equation
1370 `x = y ◇ (((z ◇ y) ◇ y) ◇ x)` and equipped with that one division. -/
private theorem aux1370_151L1 [Finite G] [Magma G] (h : Equation1370 G) (dl : G → G → G)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x : G) :
    x = dl (dl x x) (dl x x) := by
  by_contra nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X0) = X0 := mod_symm (h ..)
  have ef10 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef11 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef12 : x ≠ dl (dl x x) (dl x x) := mod_symm nh
  have ef15 (X0 X1 X2 : G) : X1 ◇ X0 = dl ((X2 ◇ X1) ◇ X1) X0 := by
    first | exact superpose ef10 ef8 | exact superpose ef8 ef10
  have ef17 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) ◇ X0 = dl X1 X0 := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  have ef44 (X0 X1 : G) : X0 ◇ X1 = dl (dl X0 X0) X1 := by
    first | exact superpose ef17 ef15 | exact superpose ef15 ef17
  have ef127 : x ≠ x ◇ (dl x x) := by
    first | exact superpose ef44 ef12 | exact superpose ef12 ef44
  subsumption ef127 ef10

theorem Equation151_termStructuralFromFin_Equation1370_finiteDivisionL :
    Law151.TermStructuralFromFin Law1370 := by
  refine termStructuralFromFin_of_leftDiv' ?_ ?_
  · intro G _ M hGL a
    exact @inj1370L G _ M (Law1370.models_iff.mp hGL) a
  · intro G _ M hGL dl h1 h2
    rw [@Law151.models_iff]
    exact fun x ↦
      @aux1370_151L1 G _ M (Law1370.models_iff.mp hGL) dl h1 h2 x

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

theorem Equation417_termStructuralFromFin_Equation1492_finiteDivisionL :
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

theorem Equation4273_termStructuralFromFin_Equation1492_finiteDivisionL :
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

theorem Equation3112_termStructuralFromFin_Equation1492_finiteDivisionR :
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

theorem Equation4588_termStructuralFromFin_Equation1492_finiteDivisionR :
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

theorem Equation417_termStructuralFromFin_Equation1496_finiteDivisionL :
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

theorem Equation429_termStructuralFromFin_Equation1496_finiteDivisionL :
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

theorem Equation440_termStructuralFromFin_Equation1496_finiteDivisionL :
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

theorem Equation452_termStructuralFromFin_Equation1496_finiteDivisionL :
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

theorem Equation4273_termStructuralFromFin_Equation1496_finiteDivisionL :
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

theorem Equation3068_termStructuralFromFin_Equation1496_finiteDivisionR :
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

theorem Equation3112_termStructuralFromFin_Equation1496_finiteDivisionR :
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

theorem Equation3152_termStructuralFromFin_Equation1496_finiteDivisionR :
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

theorem Equation3201_termStructuralFromFin_Equation1496_finiteDivisionR :
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

theorem Equation4588_termStructuralFromFin_Equation1496_finiteDivisionR :
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

/-- Right translation by `t` is injective in every finite magma satisfying equation 1648
`x = (x ◇ y) ◇ ((x ◇ y) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1648R [Finite G] [Magma G] (h : Equation1648 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have ef6 (X0 X1 : G) : (X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef7 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef8 : p ≠ q := mod_symm nh
  have ef9 : q = (p ◇ t) ◇ ((p ◇ t) ◇ t) := by
    first | exact superpose ef7 ef6 | exact superpose ef6 ef7
  have ef11 : p = q := by
    first | exact superpose ef6 ef9 | exact superpose ef9 ef6
  subsumption ef11 ef8

/-- Equation 4130 `x ◇ y = ((x ◇ y) ◇ y) ◇ x` holds of the right division of any magma satisfying
equation 1648 `x = (x ◇ y) ◇ ((x ◇ y) ◇ y)` and equipped with that one division. -/
private theorem aux1648_4130R1 [Finite G] [Magma G] (h : Equation1648 G) (dr : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (x y : G) :
    dr x y = dr (dr (dr x y) y) x := by
  by_contra nh
  have ef7 (X0 X1 : G) : (X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef9 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef10 : dr x y ≠ dr (dr (dr x y) y) x := mod_symm nh
  have ef11 (X0 X1 : G) : dr X0 X1 = X0 ◇ (X0 ◇ X1) := by
    first | exact superpose ef8 ef7 | exact superpose ef7 ef8
  have ef14 (X0 X1 : G) : dr (dr X0 X1) X1 = (dr X0 X1) ◇ X0 := by
    first | exact superpose ef8 ef11 | exact superpose ef11 ef8
  have ef62 : dr x y ≠ dr ((dr x y) ◇ x) x := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  subsumption ef62 ef9

theorem Equation4130_termStructuralFromFin_Equation1648_finiteDivisionR :
    Law4130.TermStructuralFromFin Law1648 := by
  refine termStructuralFromFin_of_rightDiv' ?_ ?_
  · intro G _ M hGL b
    exact @inj1648R G _ M (Law1648.models_iff.mp hGL) b
  · intro G _ M hGL dr h1 h2
    rw [@Law4130.models_iff]
    exact fun x y ↦
      @aux1648_4130R1 G _ M (Law1648.models_iff.mp hGL) dr h1 h2 x y

/-- Left translation by `t` is injective in every finite magma satisfying equation 1695
`x = (y ◇ x) ◇ ((y ◇ y) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1695L [Finite G] [Magma G] (h : Equation1695 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef9 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 : q = (t ◇ p) ◇ ((t ◇ t) ◇ t) := by
    first | exact superpose ef9 ef7 | exact superpose ef7 ef9
  have ef13 : p = q := by
    first | exact superpose ef7 ef11 | exact superpose ef11 ef7
  subsumption ef13 ef10

/-- Right translation by `t` is injective in every finite magma satisfying equation 1695
`x = (y ◇ x) ◇ ((y ◇ y) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1695R [Finite G] [Magma G] (h : Equation1695 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have hrot0 (a b : G) : b ◇ (a ◇ ((b ◇ b) ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ z ◇ ((b ◇ b) ◇ b)) (g := fun z ↦ b ◇ z)
      (fun z ↦ (h z b).symm) a
  have ef7 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef8 (X0 X1 : G) : X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef9 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef11 : t = (p ◇ t) ◇ ((q ◇ q) ◇ q) := by
    first | exact superpose ef9 ef7 | exact superpose ef7 ef9
  have ef12 (X0 X1 : G) : (X1 ◇ X1) ◇ X1 = X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    first | exact superpose ef7 ef7
  have ef13 (X0 : G) : ((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    first | exact superpose ef8 ef8
  have ef15 : (q ◇ q) ◇ q = t ◇ (((p ◇ t) ◇ (p ◇ t)) ◇ (p ◇ t)) := by
    first | exact superpose ef11 ef7 | exact superpose ef7 ef11
  have ef16 : (q ◇ q) ◇ q = (p ◇ p) ◇ p := by
    first | exact superpose ef12 ef15 | exact superpose ef15 ef12
  have ef25 (X0 X1 : G) :
      ((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1) = ((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1) := by
    first | exact superpose ef12 ef7 | exact superpose ef7 ef12
  have ef32 : q = ((p ◇ p) ◇ p) ◇ (((q ◇ q) ◇ (q ◇ q)) ◇ (q ◇ q)) := by
    first | exact superpose ef16 ef7 | exact superpose ef7 ef16
  have ef33 : q = ((p ◇ p) ◇ p) ◇ (((q ◇ q) ◇ q) ◇ ((q ◇ q) ◇ q)) := by
    first | exact superpose ef25 ef32 | exact superpose ef32 ef25
  have ef35 : q = ((p ◇ p) ◇ p) ◇ (((p ◇ p) ◇ p) ◇ ((p ◇ p) ◇ p)) := by
    first | exact superpose ef16 ef33 | exact superpose ef33 ef16
  have ef37 : p = q := by
    first | exact superpose ef13 ef35 | exact superpose ef35 ef13
  subsumption ef37 ef10

/-- Equation 4273 `x ◇ (x ◇ x) = y ◇ (x ◇ y)` holds of the left division of any magma satisfying
equation 1695 `x = (y ◇ x) ◇ ((y ◇ y) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux1695_4273L [Finite G] [Magma G] (h : Equation1695 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dl x (dl x x) = dl y (dl x y) := by
  by_contra nh
  have ef10 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dl x (dl x x) ≠ dl y (dl x y) := mod_symm nh
  have ef20 (X0 X1 : G) : X0 ◇ ((X1 ◇ X1) ◇ X1) = dl X1 X0 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef49 (X0 X1 : G) : (X0 ◇ X0) ◇ X0 = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef113 : dl x (dl x x) ≠ (x ◇ x) ◇ x := by
    first | exact superpose ef49 ef16 | exact superpose ef16 ef49
  subsumption ef113 ef49

theorem Equation4273_termStructuralFromFin_Equation1695_finiteDivisionL :
    Law4273.TermStructuralFromFin Law1695 := by
  refine termStructuralFromFin_of_leftDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1695R G _ M (Law1695.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1695L G _ M (Law1695.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4273.models_iff]
    exact fun x y ↦
      @aux1695_4273L G _ M (Law1695.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Equation 4588 `(x ◇ x) ◇ x = (y ◇ x) ◇ y` holds of the right division of any magma satisfying
equation 1695 `x = (y ◇ x) ◇ ((y ◇ y) ◇ y)` and equipped with two-sided divisions. -/
private theorem aux1695_4588R [Finite G] [Magma G] (h : Equation1695 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    dr (dr x x) x = dr (dr y x) y := by
  by_contra nh
  have ef10 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef14 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef15 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef16 : dr (dr x x) x ≠ dr (dr y x) y := mod_symm nh
  have ef20 (X0 X1 : G) : X0 ◇ ((X1 ◇ X1) ◇ X1) = dl X1 X0 := by
    first | exact superpose ef14 ef10 | exact superpose ef10 ef14
  have ef22 (X0 X1 : G) : (X1 ◇ X1) ◇ X1 = dl (X1 ◇ X0) X0 := by
    first | exact superpose ef10 ef15 | exact superpose ef15 ef10
  have ef23 (X0 X1 : G) : X1 ◇ X0 = dr X0 ((X1 ◇ X1) ◇ X1) := by
    first | exact superpose ef10 ef13 | exact superpose ef13 ef10
  have ef49 (X0 X1 : G) : (X0 ◇ X0) ◇ X0 = dl X1 (dl X0 X1) := by
    first | exact superpose ef20 ef15 | exact superpose ef15 ef20
  have ef74 (X0 X1 : G) : dl (X0 ◇ X0) (dl (X0 ◇ X1) X1) = X0 := by
    first | exact superpose ef22 ef15 | exact superpose ef15 ef22
  have ef101 (X0 X1 X2 : G) : X1 ◇ X2 = dr X2 (dl X0 (dl X1 X0)) := by
    first | exact superpose ef49 ef23 | exact superpose ef23 ef49
  have ef566 (X0 X1 : G) : dr X1 X0 = (X0 ◇ (X0 ◇ X0)) ◇ X1 := by
    first | exact superpose ef74 ef101 | exact superpose ef101 ef74
  have ef2919 (X0 X1 : G) : X1 ◇ (X1 ◇ X1) = dr (dr X0 X1) X0 := by
    first | exact superpose ef566 ef13 | exact superpose ef13 ef566
  have ef8081 : dr (dr x x) x ≠ x ◇ (x ◇ x) := by
    first | exact superpose ef2919 ef16 | exact superpose ef16 ef2919
  subsumption ef8081 ef2919

theorem Equation4588_termStructuralFromFin_Equation1695_finiteDivisionR :
    Law4588.TermStructuralFromFin Law1695 := by
  refine termStructuralFromFin_of_rightDiv ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj1695R G _ M (Law1695.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj1695L G _ M (Law1695.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law4588.models_iff]
    exact fun x y ↦
      @aux1695_4588R G _ M (Law1695.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 1722
`x = (y ◇ y) ◇ ((x ◇ y) ◇ y)`. Its models are therefore quasigroups, and the division is the
inverse translation -- a term, at an exponent the carrier fixes. -/
private theorem inj1722R [Finite G] [Magma G] (h : Equation1722 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have ef8 (X0 X1 : G) : (X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef11 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef13 : q = (t ◇ t) ◇ ((p ◇ t) ◇ t) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef15 : p = q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef15 ef12

/-- Equation 2441 `x = (x ◇ ((x ◇ x) ◇ x)) ◇ x` holds of the right division of any magma satisfying
equation 1722 `x = (y ◇ y) ◇ ((x ◇ y) ◇ y)` and equipped with that one division. -/
private theorem aux1722_2441R1 [Finite G] [Magma G] (h : Equation1722 G) (dr : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (x : G) :
    x = dr (dr x (dr (dr x x) x)) x := by
  by_contra nh
  have ef9 (X0 X1 : G) : (X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef14 : x ≠ dr (dr x (dr (dr x x) x)) x := mod_symm nh
  have ef15 (X0 X1 : G) : (X1 ◇ X1) ◇ (X0 ◇ X1) = dr X0 X1 := by
    first | exact superpose ef12 ef9 | exact superpose ef9 ef12
  have ef17 (X0 X1 : G) : X1 ◇ X1 = dr X0 ((X0 ◇ X1) ◇ X1) := by
    first | exact superpose ef9 ef13 | exact superpose ef13 ef9
  have ef28 (X0 X1 : G) : (X1 ◇ X1) ◇ X0 = dr (dr X0 X1) X1 := by
    first | exact superpose ef12 ef15 | exact superpose ef15 ef12
  have ef93 : x ≠ dr (dr x ((x ◇ x) ◇ x)) x := by
    first | exact superpose ef28 ef14 | exact superpose ef14 ef28
  have ef94 : x ≠ dr (x ◇ x) x := by
    first | exact superpose ef17 ef93 | exact superpose ef93 ef17
  subsumption ef94 ef13

theorem Equation2441_termStructuralFromFin_Equation1722_finiteDivisionR :
    Law2441.TermStructuralFromFin Law1722 := by
  refine termStructuralFromFin_of_rightDiv' ?_ ?_
  · intro G _ M hGL b
    exact @inj1722R G _ M (Law1722.models_iff.mp hGL) b
  · intro G _ M hGL dr h1 h2
    rw [@Law2441.models_iff]
    exact fun x ↦
      @aux1722_2441R1 G _ M (Law1722.models_iff.mp hGL) dr h1 h2 x

/-- Equation 3105 `x = (((y ◇ x) ◇ x) ◇ y) ◇ x` holds of the right division of any magma satisfying
equation 1722 `x = (y ◇ y) ◇ ((x ◇ y) ◇ y)` and equipped with that one division. -/
private theorem aux1722_3105R1 [Finite G] [Magma G] (h : Equation1722 G) (dr : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (x y : G) :
    x = dr (dr (dr (dr y x) x) y) x := by
  by_contra nh
  have ef9 (X0 X1 : G) : (X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef13 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef14 : x ≠ dr (dr (dr (dr y x) x) y) x := mod_symm nh
  have ef15 (X0 X1 : G) : (X1 ◇ X1) ◇ (X0 ◇ X1) = dr X0 X1 := by
    first | exact superpose ef12 ef9 | exact superpose ef9 ef12
  have ef28 (X0 X1 : G) : (X1 ◇ X1) ◇ X0 = dr (dr X0 X1) X1 := by
    first | exact superpose ef12 ef15 | exact superpose ef15 ef12
  have ef93 : x ≠ dr (dr ((x ◇ x) ◇ y) y) x := by
    first | exact superpose ef28 ef14 | exact superpose ef14 ef28
  have ef94 : x ≠ dr (x ◇ x) x := by
    first | exact superpose ef13 ef93 | exact superpose ef93 ef13
  subsumption ef94 ef13

theorem Equation3105_termStructuralFromFin_Equation1722_finiteDivisionR :
    Law3105.TermStructuralFromFin Law1722 := by
  refine termStructuralFromFin_of_rightDiv' ?_ ?_
  · intro G _ M hGL b
    exact @inj1722R G _ M (Law1722.models_iff.mp hGL) b
  · intro G _ M hGL dr h1 h2
    rw [@Law3105.models_iff]
    exact fun x y ↦
      @aux1722_3105R1 G _ M (Law1722.models_iff.mp hGL) dr h1 h2 x y

end Law.MagmaLaw
