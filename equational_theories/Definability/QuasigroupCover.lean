import equational_theories.Definability.QuasigroupWitness
import equational_theories.Equations.All
import equational_theories.Superposition

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
-- a cell rarely needs all four division axioms, and which ones it needs is Vampire's business
set_option linter.unusedVariables false

/-!
# Term-definability facts whose witness divides

The sources below all have the chain shape `x = h_k (⋯ (h_1 x) ⋯)` with every `h_i` a translation,
so on a finite carrier every translation is a bijection and the models are quasigroups. That buys
more than the cyclic rotations `Definability/PositiveTermsFin.lean` uses: as
`Definability/QuasigroupWitness.lean` shows, the two divisions are themselves magma terms, iterated
translations at an exponent read off the carrier. The defining term may therefore be sought in the
clone of `◇`, `/` and `\`, which is strictly larger than the clone of `◇` that the sweeps behind
`PositiveTermsFin.lean` exhausted.

Each cell contributes three replayed lemmas: `inj<s>R` and `inj<s>L`, which say the source forces
both translations injective and so hand `termDefinableFromFin_of_qterm` its divisions, and
`aux<s>_<t>`, which says the target law holds of the witness in any structure carrying two-sided
divisions. The witness enters `aux` as an abstract `wf` pinned by `hwdef` rather than as an unfolded
term: substituting a five-leaf witness into a six-leaf target gives a thirty-leaf goal that
superposition drowns in, whereas the definition lets each unfolding happen where it is needed.
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

/-- Right translation by `t` is injective in every finite magma satisfying equation 467
`x = y ◇ (x ◇ (x ◇ (y ◇ y)))`. Its models are quasigroups, which is what lets
`termDefinableFromFin_of_qterm` spend divisions. -/
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
`x = y ◇ (x ◇ (x ◇ (y ◇ y)))`. Its models are quasigroups, which is what lets
`termDefinableFromFin_of_qterm` spend divisions. -/
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

/-- Equation 504 `x = y ◇ (y ◇ (x ◇ (y ◇ y)))` holds of the operation `x □ y := (y◇(y◇x))` in every
magma satisfying equation 467 `x = y ◇ (x ◇ (x ◇ (y ◇ y)))` and equipped with two-sided
divisions. -/
private theorem aux467_504 [Finite G] [Magma G] (h : Equation467 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = b ◇ (b ◇ a))
    (x y : G) :
    x = wf y (wf y (wf x (wf y y))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef11 (X0 X1 : G) : X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef13 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef16 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef17 (X0 X1 : G) : wf X0 X1 = X1 ◇ (X1 ◇ X0) := mod_symm (hwdef ..)
  have ef18 : x ≠ wf y (wf y (wf x (wf y y))) := mod_symm nh
  have ef19 (X0 X1 : G) : wf (X1 ◇ X1) (X1 ◇ X0) = X0 := by
    first | exact superpose ef17 ef12 | exact superpose ef12 ef17
  have ef20 (X0 X1 : G) : X1 ◇ (wf (X1 ◇ X1) X0) = X0 := by
    first | exact superpose ef17 ef11 | exact superpose ef11 ef17
  have ef23 (X0 X1 : G) : wf X1 (dr X0 X1) = (dr X0 X1) ◇ X0 := by
    first | exact superpose ef13 ef17 | exact superpose ef17 ef13
  have ef26 (X0 X1 : G) : X1 ◇ X0 = dl X1 (wf X0 X1) := by
    first | exact superpose ef17 ef16 | exact superpose ef16 ef17
  have ef31 (X0 X1 : G) : wf (X1 ◇ X1) X0 = dl X1 X0 := by
    first | exact superpose ef15 ef19 | exact superpose ef19 ef15
  have ef32 (X0 X1 : G) : X1 ◇ X0 = wf (X1 ◇ X1) (wf X0 X1) := by
    first | exact superpose ef17 ef19 | exact superpose ef19 ef17
  have ef66 (X0 X1 : G) : X1 ◇ (X0 ◇ X0) = dl X1 (dl X0 X1) := by
    first | exact superpose ef31 ef26 | exact superpose ef26 ef31
  have ef74 (X0 X1 : G) : dr X0 (X1 ◇ X1) = X1 ◇ ((dr X0 (X1 ◇ X1)) ◇ X0) := by
    first | exact superpose ef23 ef20 | exact superpose ef20 ef23
  have ef199 (X0 X1 : G) : X1 ◇ X1 = dl X0 (dl X0 (dl X1 X0)) := by
    first | exact superpose ef66 ef16 | exact superpose ef16 ef66
  have ef212 (X0 X1 : G) : X1 ◇ X1 = dl (X1 ◇ X0) (dl (X1 ◇ X0) X0) := by
    first | exact superpose ef16 ef199 | exact superpose ef199 ef16
  have ef432 (X0 : G) : X0 ◇ (X0 ◇ X0) = dr (X0 ◇ X0) (X0 ◇ X0) := by
    first | exact superpose ef13 ef74 | exact superpose ef74 ef13
  have ef446 (X0 : G) : wf X0 X0 = dr (X0 ◇ X0) (X0 ◇ X0) := by
    first | exact superpose ef17 ef432 | exact superpose ef432 ef17
  have ef462 (X0 : G) : X0 ◇ X0 = (wf X0 X0) ◇ (X0 ◇ X0) := by
    first | exact superpose ef446 ef13 | exact superpose ef13 ef446
  have ef1046 (X0 : G) : (wf X0 X0) ◇ (wf X0 X0) = dl (X0 ◇ X0) (dl (X0 ◇ X0) (X0 ◇ X0)) := by
    first | exact superpose ef462 ef212 | exact superpose ef212 ef462
  have ef1061 (X0 : G) : (wf X0 X0) ◇ (wf X0 X0) = (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    first | exact superpose ef66 ef1046 | exact superpose ef1046 ef66
  have ef1069 (X0 : G) : wf (X0 ◇ X0) (X0 ◇ X0) = (wf X0 X0) ◇ (wf X0 X0) := by
    first | exact superpose ef17 ef1061 | exact superpose ef1061 ef17
  have ef1071 (X0 : G) : (wf X0 X0) ◇ (wf X0 X0) = X0 := by
    first | exact superpose ef19 ef1069 | exact superpose ef1069 ef19
  have ef1139 (X0 X1 : G) : wf X0 ((wf X0 X0) ◇ X1) = X1 := by
    first | exact superpose ef1071 ef19 | exact superpose ef19 ef1071
  have ef1142 (X0 X1 : G) : (wf X0 X0) ◇ X1 = wf X0 (wf X1 (wf X0 X0)) := by
    first | exact superpose ef1071 ef32 | exact superpose ef32 ef1071
  have ef13423 : x ≠ wf y ((wf y y) ◇ x) := by
    first | exact superpose ef1142 ef18 | exact superpose ef18 ef1142
  subsumption ef13423 ef1139

theorem Equation504_termDefinableFromFin_Equation467 :
    Law504.TermDefinableFromFin Law467 := by
  refine termDefinableFromFin_of_qterm (.op (.var 1) (.op (.var 1) (.var 0))) ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj467R G _ M (Law467.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj467L G _ M (Law467.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law504.models_iff]
    exact fun x y ↦
      @aux467_504 G _ M (Law467.models_iff.mp hGL) dr dl h1 h2 h3 h4 _ (fun _ _ ↦ rfl) x y

/-- Right translation by `t` is injective in every finite magma satisfying equation 898
`x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. Its models are quasigroups, which is what lets
`termDefinableFromFin_of_qterm` spend divisions. -/
private theorem inj898R [Finite G] [Magma G] (h : Equation898 G) (t : G) :
    Function.Injective (fun p : G ↦ p ◇ t) := by
  intro p q hhyp
  replace hhyp : p ◇ t = q ◇ t := hhyp
  by_contra nh
  have ef8 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef11 : p ◇ t = q ◇ t := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef13 (X0 : G) : q = X0 ◇ ((p ◇ t) ◇ (t ◇ X0)) := by
    first | exact superpose ef11 ef8 | exact superpose ef8 ef11
  have ef18 : p = q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  subsumption ef18 ef12

/-- Left translation by `t` is injective in every finite magma satisfying equation 898
`x = y ◇ ((x ◇ z) ◇ (z ◇ y))`. Its models are quasigroups, which is what lets
`termDefinableFromFin_of_qterm` spend divisions. -/
private theorem inj898L [Finite G] [Magma G] (h : Equation898 G) (t : G) :
    Function.Injective (fun p : G ↦ t ◇ p) := by
  intro p q hhyp
  replace hhyp : t ◇ p = t ◇ q := hhyp
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef11 : t ◇ p = t ◇ q := mod_symm hhyp
  have ef12 : p ≠ q := mod_symm nh
  have ef25 (X0 : G) : q = ((t ◇ p) ◇ X0) ◇ (X0 ◇ t) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef38 : p = q := by
    first | exact superpose ef10 ef25 | exact superpose ef25 ef10
  subsumption ef38 ef12

set_option maxHeartbeats 20000000 in
/-- Equation 504 `x = y ◇ (y ◇ (x ◇ (y ◇ y)))` holds of the operation
`x □ y := (((x/x)\((x◇x)◇(y◇y)))/(x◇y))` in every magma satisfying equation 898
`x = y ◇ ((x ◇ z) ◇ (z ◇ y))` and equipped with two-sided divisions. -/
private theorem aux898_504 [Finite G] [Magma G] (h : Equation898 G) (dr dl : G → G → G)
    (hrs : ∀ a b : G, dr a b ◇ b = a) (hri : ∀ a b : G, dr (a ◇ b) b = a)
    (hls : ∀ a b : G, a ◇ dl a b = b) (hli : ∀ a b : G, dl a (a ◇ b) = b)
    (x y : G) :
    x = dr (dl (dr y y) ((y ◇ y) ◇
      ((dr (dl (dr y y) ((y ◇ y) ◇ ((dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))) ◇ (dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))))) (y ◇
      (dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇
      (dr (dl (dr y y) ((y ◇ y) ◇ ((dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))) ◇ (dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))))) (y ◇
      (dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))))))) (y ◇
      (dr (dl (dr y y) ((y ◇ y) ◇
      ((dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))) ◇
      (dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))))) (y ◇
      (dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇
      (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))))) := by
  by_contra nh
  have hrot0 (a b c : G) : (b ◇ (a ◇ (c ◇ b))) ◇ c = a :=
    rot_of_finite (f := fun z ↦ b ◇ (z ◇ (c ◇ b))) (g := fun z ↦ z ◇ c)
      (fun z ↦ (h z b c).symm) a
  have hrot1 (a b c : G) : ((b ◇ a) ◇ c) ◇ (c ◇ b) = a :=
    rot_of_finite (f := fun z ↦ (b ◇ z) ◇ c) (g := fun z ↦ z ◇ (c ◇ b))
      (fun z ↦ hrot0 z b c) a
  have ef11 (X0 X1 X2 : G) : X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have ef12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X2 = X0 := mod_symm (hrot0 ..)
  have ef13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X1) = X0 := mod_symm (hrot1 ..)
  have ef14 (X0 X1 : G) : (dr X0 X1) ◇ X1 = X0 := mod_symm (hrs ..)
  have ef15 (X0 X1 : G) : dr (X0 ◇ X1) X1 = X0 := mod_symm (hri ..)
  have ef16 (X0 X1 : G) : X0 ◇ (dl X0 X1) = X1 := mod_symm (hls ..)
  have ef17 (X0 X1 : G) : dl X0 (X0 ◇ X1) = X1 := mod_symm (hli ..)
  have ef18 :
      x ≠ dr (dl (dr y y) ((y ◇ y) ◇
      ((dr (dl (dr y y) ((y ◇ y) ◇ ((dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))) ◇ (dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))))) (y ◇
      (dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇
      (dr (dl (dr y y) ((y ◇ y) ◇ ((dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))) ◇ (dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))))) (y ◇
      (dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))))))) (y ◇
      (dr (dl (dr y y) ((y ◇ y) ◇
      ((dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))) ◇
      (dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))))) (y ◇
      (dr (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))) (x ◇
      (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y))))))) := mod_symm nh
  have ef19 (X0 X1 : G) : dr X0 (dl X1 X0) = X1 := by
    first | exact superpose ef16 ef15 | exact superpose ef15 ef16
  have ef25 (X0 X1 X2 : G) : X1 ◇ (X0 ◇ (X2 ◇ X1)) = dr X0 X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef28 (X0 X1 X2 : G) : X1 ◇ ((X2 ◇ (dr X0 X1)) ◇ X0) = X2 := by
    first | exact superpose ef14 ef11 | exact superpose ef11 ef14
  have ef29 (X0 X1 X2 : G) : (dl X1 X0) ◇ ((X2 ◇ X1) ◇ X0) = X2 := by
    first | exact superpose ef16 ef11 | exact superpose ef11 ef16
  have ef32 (X0 X1 X2 : G) : (X0 ◇ X2) ◇ (X2 ◇ X1) = dl X1 X0 := by
    first | exact superpose ef11 ef17 | exact superpose ef17 ef11
  have ef34 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) ◇ (dr X0 X1) = X2 := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef35 (X0 X1 X2 : G) : ((dl X1 X0) ◇ (X2 ◇ X0)) ◇ X1 = X2 := by
    first | exact superpose ef16 ef12 | exact superpose ef12 ef16
  have ef38 (X0 X1 X2 : G) : (X1 ◇ X0) ◇ X2 = dr X0 (X2 ◇ X1) := by
    first | exact superpose ef14 ef12 | exact superpose ef12 ef14
  have ef51 (X0 X1 X2 : G) : X0 ◇ ((dl (X1 ◇ X2) X0) ◇ X1) = X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef53 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (dr X0 X1)) ◇ X0 = X2 := by
    first | exact superpose ef14 ef13 | exact superpose ef13 ef14
  have ef54 (X0 X1 X2 : G) : (((dl X1 X0) ◇ X2) ◇ X1) ◇ X0 = X2 := by
    first | exact superpose ef16 ef13 | exact superpose ef13 ef16
  have ef57 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0 = X3 := by
    first | exact superpose ef13 ef13
  have ef59 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X0) = X3 := by
    first | exact superpose ef13 ef11 | exact superpose ef11 ef13
  have ef60 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X1) = X3 := by
    first | exact superpose ef13 ef12 | exact superpose ef12 ef13
  have ef62 (X0 X1 X2 : G) : X2 ◇ X1 = dl ((X1 ◇ X0) ◇ X2) X0 := by
    first | exact superpose ef13 ef17 | exact superpose ef17 ef13
  have ef63 (X0 X1 X2 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (dr X0 X1) := by
    first | exact superpose ef14 ef25 | exact superpose ef25 ef14
  have ef64 (X0 X1 X2 : G) : (dl X1 X0) ◇ (X2 ◇ X0) = dr X2 X1 := by
    first | exact superpose ef16 ef25 | exact superpose ef25 ef16
  have ef71 (X0 X1 X2 : G) : (X1 ◇ X2) ◇ (dr X0 X1) = dr X2 X0 := by
    first | exact superpose ef25 ef25
  have ef85 (X0 X1 X2 : G) : X0 ◇ (X1 ◇ X2) = dl X2 (dr X0 X1) := by
    first | exact superpose ef25 ef17 | exact superpose ef17 ef25
  have ef106 (X0 X1 X2 : G) : dl X1 X0 = (X0 ◇ (dr X2 X1)) ◇ X2 := by
    first | exact superpose ef28 ef17 | exact superpose ef17 ef28
  have ef137 (X0 X1 X2 : G) : (X0 ◇ X1) ◇ X2 = dl (dl X1 X2) X0 := by
    first | exact superpose ef29 ef17 | exact superpose ef17 ef29
  have ef138 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0) = dr X3 (dl X1 X2) := by
    first | exact superpose ef29 ef25 | exact superpose ef25 ef29
  have ef141 (X0 X1 X2 : G) : dl X2 X1 = X0 ◇ ((dl X1 X0) ◇ X2) := by
    first | exact superpose ef16 ef32 | exact superpose ef32 ef16
  have ef146 (X0 X1 X2 X3 : G) : dl X3 ((X1 ◇ X0) ◇ X2) = X0 ◇ ((X2 ◇ X1) ◇ X3) := by
    first | exact superpose ef13 ef32 | exact superpose ef32 ef13
  have ef147 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ X2) = (dl X0 X1) ◇ ((X2 ◇ X0) ◇ X3) := by
    first | exact superpose ef32 ef32
  have ef149 (X0 X1 X2 X3 : G) : dl X3 (dl X1 X2) = X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3) := by
    first | exact superpose ef29 ef32 | exact superpose ef32 ef29
  have ef152 (X0 X1 X2 X3 : G) : dl (X0 ◇ (X1 ◇ X3)) X2 = (X2 ◇ X3) ◇ (dr X0 X1) := by
    first | exact superpose ef25 ef32 | exact superpose ef32 ef25
  have ef153 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ X0 = dl ((X0 ◇ (dr X3 X2)) ◇ X3) X1 := by
    first | exact superpose ef28 ef32 | exact superpose ef32 ef28
  have ef158 (X0 X1 X2 X3 : G) : dl ((X0 ◇ X2) ◇ X3) X1 = (X1 ◇ (dl X2 X3)) ◇ X0 := by
    first | exact superpose ef29 ef32 | exact superpose ef32 ef29
  have ef176 (X0 X1 X2 : G) : X2 ◇ X0 = dl (X1 ◇ X2) (dl X0 X1) := by
    first | exact superpose ef32 ef17 | exact superpose ef17 ef32
  have ef177 (X0 X1 X2 X3 : G) : dr X3 (X1 ◇ X2) = (X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1)) := by
    first | exact superpose ef32 ef25 | exact superpose ef25 ef32
  have ef218 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = dr X3 (X2 ◇ (X0 ◇ X1)) := by
    first | exact superpose ef34 ef25 | exact superpose ef25 ef34
  have ef220 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (X0 ◇ X2)) = X0 ◇ ((dr X2 X1) ◇ X3) := by
    first | exact superpose ef34 ef32 | exact superpose ef32 ef34
  have ef221 (X0 X1 X2 X3 : G) : dl (dr X3 X2) X1 = (X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X0 := by
    first | exact superpose ef34 ef32 | exact superpose ef32 ef34
  have ef241 (X0 X1 X2 : G) : dr X0 X2 = ((dl X1 X2) ◇ X0) ◇ X1 := by
    first | exact superpose ef14 ef35 | exact superpose ef35 ef14
  have ef284 :
      x ≠ dr (dl (dr y y) ((y ◇ y) ◇
      ((dr (dl (dr y y) ((y ◇ y) ◇ ((((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x) ◇ (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x)))) (y ◇
      (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x))) ◇
      (dr (dl (dr y y) ((y ◇ y) ◇ ((((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x) ◇ (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x)))) (y ◇
      (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x)))))) (y ◇
      (dr (dl (dr y y) ((y ◇ y) ◇
      ((((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x) ◇
      (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x)))) (y ◇
      (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇
      (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇
      x)))) := by
    first | exact superpose ef38 ef18 | exact superpose ef18 ef38
  have ef290 :
      x ≠ ((dr (dl (dr y y) ((y ◇ y) ◇
      ((((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x) ◇
      (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x)))) (y ◇
      (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇
      (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇
      x))) ◇ (dl (dr y y) ((y ◇ y) ◇
      ((dr (dl (dr y y) ((y ◇ y) ◇ ((((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x) ◇ (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x)))) (y ◇ (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x))) ◇
      (dr (dl (dr y y) ((y ◇ y) ◇ ((((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x) ◇ (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x)))) (y ◇ (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x))))))) ◇
      y := by
    first | exact superpose ef38 ef284 | exact superpose ef284 ef38
  have ef296 :
      x ≠ ((((((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇
      (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇
      x) ◇ (dl (dr y y) ((y ◇ y) ◇
      ((((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x) ◇ (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x))))) ◇
      y) ◇ (dl (dr y y) ((y ◇ y) ◇
      ((((((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x) ◇ (dl (dr y y) ((y ◇ y) ◇ ((((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x) ◇ (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x))))) ◇
      y) ◇
      (((((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x) ◇ (dl (dr y y) ((y ◇ y) ◇ ((((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x) ◇ (((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dl (dr x x) ((x ◇ x) ◇ ((dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)) ◇ (dr (dl (dr y y) ((y ◇ y) ◇ (y ◇ y))) (y ◇ y)))))) ◇ x))))) ◇
      y))))) ◇ y := by
    first | exact superpose ef38 ef290 | exact superpose ef290 ef38
  have ef300 :
      x ≠ (((((((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇
      (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ ((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y))))) ◇
      x) ◇ (dl (dr y y) ((y ◇ y) ◇
      (((((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ ((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ ((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y))))) ◇ x))))) ◇
      y) ◇ (dl (dr y y) ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ ((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y))))) ◇ x) ◇ (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ ((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ ((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ ((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y))))) ◇ x) ◇ (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ ((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y) ◇ ((y ◇ (dl (dr y y) ((y ◇ y) ◇ (y ◇ y)))) ◇ y))))) ◇ x))))) ◇
      y))))) ◇ y := by
    first | exact superpose ef38 ef296 | exact superpose ef296 ef38
  have ef304 :
      x ≠ (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇ (dl (dr y y) ((y ◇ y) ◇
      (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇ (dl (dr y y) ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))))) ◇ y := by
    first | exact superpose ef32 ef300 | exact superpose ef300 ef32
  have ef324 (X0 X1 X2 : G) : X0 ◇ (dr X2 X1) = dl (X2 ◇ X0) X1 := by
    first | exact superpose ef51 ef34 | exact superpose ef34 ef51
  have ef360 (X0 X1 X2 X3 : G) : X2 ◇ X1 = (X0 ◇ (dr X3 ((X1 ◇ X0) ◇ X2))) ◇ X3 := by
    first | exact superpose ef13 ef53 | exact superpose ef53 ef13
  have ef362 (X0 X1 X2 X3 : G) : dr X2 X1 = (X0 ◇ (dr X3 (X1 ◇ (X0 ◇ X2)))) ◇ X3 := by
    first | exact superpose ef34 ef53 | exact superpose ef53 ef34
  have ef377 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 ((X3 ◇ X0) ◇ (dr X1 X3)) := by
    first | exact superpose ef53 ef25 | exact superpose ef25 ef53
  have ef392 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = ((dr X1 X3) ◇ X2) ◇ (X3 ◇ X0) := by
    first | exact superpose ef38 ef377 | exact superpose ef377 ef38
  have ef396 (X0 X1 X2 X3 : G) : dr X2 X1 = (X0 ◇ (((X0 ◇ X2) ◇ X3) ◇ X1)) ◇ X3 := by
    first | exact superpose ef38 ef362 | exact superpose ef362 ef38
  have ef398 (X0 X1 X2 X3 : G) : X2 ◇ X1 = (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) ◇ X3 := by
    first | exact superpose ef38 ef360 | exact superpose ef360 ef38
  have ef404 (X1 X2 X3 : G) : X2 ◇ X1 = (dr (X2 ◇ X3) X1) ◇ X3 := by
    first | exact superpose ef25 ef398 | exact superpose ef398 ef25
  have ef410 (X0 X1 X2 X3 : G) : X0 ◇ (X1 ◇ (dl X2 X3)) = ((dr X0 X1) ◇ X2) ◇ X3 := by
    first | exact superpose ef25 ef54 | exact superpose ef54 ef25
  have ef424 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = dr X2 (((dl X3 X1) ◇ X0) ◇ X3) := by
    first | exact superpose ef54 ef25 | exact superpose ef25 ef54
  have ef444 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ X0) = (X3 ◇ X2) ◇ ((dl X3 X1) ◇ X0) := by
    first | exact superpose ef38 ef424 | exact superpose ef424 ef38
  have ef462 (X0 X1 X2 X3 : G) : X1 ◇ (X2 ◇ (X0 ◇ X3)) = dl (X0 ◇ X1) (dr X3 X2) := by
    first | exact superpose ef34 ef62 | exact superpose ef62 ef34
  have ef514 (X0 X1 X2 X3 : G) : (dl X1 (X2 ◇ X3)) ◇ X0 = dr ((X3 ◇ X0) ◇ X2) X1 := by
    first | exact superpose ef13 ef64 | exact superpose ef64 ef13
  have ef517 (X0 X1 X2 : G) : (dl X1 X2) ◇ X0 = dr (dr X0 X2) X1 := by
    first | exact superpose ef14 ef64 | exact superpose ef64 ef14
  have ef527 (X0 X1 X2 : G) : X2 ◇ (dr X0 X1) = dr (dl X1 X2) X0 := by
    first | exact superpose ef64 ef25 | exact superpose ef25 ef64
  have ef538 (X0 X1 X2 X3 : G) : dr X3 (dl X1 X2) = (X0 ◇ X2) ◇ (X3 ◇ (dr X0 X1)) := by
    first | exact superpose ef64 ef25 | exact superpose ef25 ef64
  have ef567 (X0 X1 X2 X3 : G) : (dr X0 X1) ◇ (dr X3 X2) = dr (X0 ◇ (X1 ◇ X2)) X3 := by
    first | exact superpose ef25 ef71 | exact superpose ef71 ef25
  have ef571 (X0 X1 X2 X3 : G) : dr X2 X3 = X0 ◇ (dr X3 (((dl X1 X2) ◇ X0) ◇ X1)) := by
    first | exact superpose ef54 ef71 | exact superpose ef71 ef54
  have ef636 (X0 X1 X2 X3 : G) : dr X2 X3 = X0 ◇ ((X1 ◇ X3) ◇ ((dl X1 X2) ◇ X0)) := by
    first | exact superpose ef38 ef571 | exact superpose ef571 ef38
  have ef647 (X1 X2 X3 : G) : dr X2 X3 = dr (X1 ◇ X3) (dl X1 X2) := by
    first | exact superpose ef25 ef636 | exact superpose ef636 ef25
  have ef701 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ (dr X2 X0)) = (dl X0 X1) ◇ (X2 ◇ X3) := by
    first | exact superpose ef106 ef32 | exact superpose ef32 ef106
  have ef709 (X0 X1 X2 X3 : G) : (dl X2 X3) ◇ (dl X0 X1) = dr (X1 ◇ (dr X3 X0)) X2 := by
    first | exact superpose ef106 ef64 | exact superpose ef64 ef106
  have ef946 (X0 X1 X2 : G) : dl X1 (dl X2 X0) = (dl X0 X1) ◇ X2 := by
    first | exact superpose ef141 ef35 | exact superpose ef35 ef141
  have ef1257 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = dr X3 ((dl X2 X1) ◇ X0) := by
    first | exact superpose ef241 ef25 | exact superpose ef25 ef241
  have ef1285 (X0 X1 X2 X3 : G) : X2 ◇ ((dr X0 X1) ◇ X3) = (dl (dr X3 X2) X1) ◇ X0 := by
    first | exact superpose ef241 ef28 | exact superpose ef28 ef241
  have ef1298 (X0 X1 X2 X3 : G) : X2 ◇ (X3 ◇ (dr X0 X1)) = (X0 ◇ X3) ◇ (dl X2 X1) := by
    first | exact superpose ef38 ef1257 | exact superpose ef1257 ef38
  have ef1451 (X0 X1 X2 X3 : G) : dl (dl X0 X1) X3 = (X2 ◇ X0) ◇ (dr (X1 ◇ X2) X3) := by
    first | exact superpose ef32 ef324 | exact superpose ef324 ef32
  have ef1453 (X0 X1 X2 X3 : G) : dl (dr X0 X1) X3 = (dr X1 X2) ◇ (dr (X2 ◇ X0) X3) := by
    first | exact superpose ef71 ef324 | exact superpose ef324 ef71
  have ef1478 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X0)) ◇ X2 = dl (X0 ◇ (dr X1 X2)) X3 := by
    first | exact superpose ef324 ef137 | exact superpose ef137 ef324
  have ef1479 (X0 X1 X2 X3 : G) : dl X3 (X1 ◇ X0) = X2 ◇ ((X0 ◇ (dr X1 X2)) ◇ X3) := by
    first | exact superpose ef324 ef141 | exact superpose ef141 ef324
  have ef1492 (X0 X1 X2 X3 : G) : (X3 ◇ (X1 ◇ X0)) ◇ X2 = (dr X1 X2) ◇ (dr X0 X3) := by
    first | exact superpose ef324 ef1478 | exact superpose ef1478 ef324
  have ef1502 (X0 X1 X2 X3 : G) : (X3 ◇ X0) ◇ X1 = (X2 ◇ X0) ◇ (dr (X1 ◇ X2) X3) := by
    first | exact superpose ef137 ef1451 | exact superpose ef1451 ef137
  have ef1605 (X0 X1 X2 X3 : G) : (dr X0 X3) ◇ ((X0 ◇ X1) ◇ X2) = (dl X1 X2) ◇ X3 := by
    first | exact superpose ef29 ef404 | exact superpose ef404 ef29
  have ef1885 (X0 X1 X2 X3 : G) : dl (X1 ◇ X2) X0 = (X0 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3 := by
    first | exact superpose ef16 ef57 | exact superpose ef57 ef16
  have ef2032 (X0 X1 X2 X3 : G) : X2 ◇ (dr X1 X0) = (X0 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X3 := by
    first | exact superpose ef324 ef1885 | exact superpose ef1885 ef324
  have ef2374 (X0 X1 X2 X3 : G) : (X1 ◇ X0) ◇ (X2 ◇ X3) = (X1 ◇ X2) ◇ (X0 ◇ X3) := by
    first | exact superpose ef13 ef59 | exact superpose ef59 ef13
  have ef2625 (X0 X1 X2 X3 : G) : X2 ◇ X3 = X0 ◇ (((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X2)) := by
    first | exact superpose ef60 ef60
  have ef2716 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)) = dl (X0 ◇ X1) ((X3 ◇ X4) ◇ X2) := by
    first | exact superpose ef60 ef62 | exact superpose ef62 ef60
  have ef2748 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)) = X1 ◇ (dr X0 ((X3 ◇ X4) ◇ X2)) := by
    first | exact superpose ef324 ef2716 | exact superpose ef2716 ef324
  have ef2795 (X0 X2 X3 : G) : X2 ◇ X3 = X0 ◇ (dl X2 (X0 ◇ X3)) := by
    first | exact superpose ef32 ef2625 | exact superpose ef2625 ef32
  have ef2827 (X0 X1 X2 X3 X4 : G) :
      X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4)) = X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4)) := by
    first | exact superpose ef38 ef2748 | exact superpose ef2748 ef38
  have ef2886 (X0 X1 X2 X3 : G) : X1 ◇ ((X0 ◇ X2) ◇ X3) = (dl X2 X3) ◇ (dl X1 X0) := by
    first | exact superpose ef29 ef2795 | exact superpose ef2795 ef29
  have ef2926 (X0 X1 X2 X3 : G) : (dl X0 (X2 ◇ X1)) ◇ X3 = dl (X0 ◇ X1) (dl X3 X2) := by
    first | exact superpose ef2795 ef176 | exact superpose ef176 ef2795
  have ef2948 (X0 X1 X2 X3 : G) : (dl X0 (X2 ◇ X1)) ◇ X3 = X1 ◇ (dr X0 (dl X3 X2)) := by
    first | exact superpose ef324 ef2926 | exact superpose ef2926 ef324
  have ef8476 (X0 X1 X2 X3 : G) : (X0 ◇ X3) ◇ (X3 ◇ X1) = dl (dr X0 (dl X1 X2)) X2 := by
    first | exact superpose ef138 ef62 | exact superpose ef62 ef138
  have ef8486 (X0 X1 X2 : G) : dl X1 X0 = dl (dr X0 (dl X1 X2)) X2 := by
    first | exact superpose ef32 ef8476 | exact superpose ef8476 ef32
  have ef10489 (X0 X1 X2 X3 : G) : X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3) = (dl X2 X3) ◇ X1 := by
    first | exact superpose ef946 ef149 | exact superpose ef149 ef946
  have ef10490 (X0 X1 X2 X3 : G) : (X2 ◇ X3) ◇ (dr X0 X1) = (X1 ◇ X3) ◇ (dr X0 X2) := by
    first | exact superpose ef324 ef152 | exact superpose ef152 ef324
  have ef10491 (X0 X1 X2 X3 : G) : (X1 ◇ X2) ◇ X0 = X3 ◇ (dr (X0 ◇ (dr X3 X2)) X1) := by
    first | exact superpose ef324 ef153 | exact superpose ef153 ef324
  have ef10722 (X0 X1 X2 X3 : G) : (X1 ◇ (dl X2 X3)) ◇ X0 = X3 ◇ (dr (X0 ◇ X2) X1) := by
    first | exact superpose ef324 ef158 | exact superpose ef158 ef324
  have ef11293 (X0 X1 X2 X3 : G) : (X2 ◇ X0) ◇ (X3 ◇ (dl X0 X1)) = (X2 ◇ X3) ◇ X1 := by
    first | exact superpose ef38 ef177 | exact superpose ef177 ef38
  have ef12879 (X0 X1 X2 X3 : G) : (dr X1 X2) ◇ (X3 ◇ X0) = ((X0 ◇ X1) ◇ X3) ◇ X2 := by
    first | exact superpose ef38 ef218 | exact superpose ef218 ef38
  have ef18347 (X0 X1 X2 X3 : G) : X3 ◇ (X2 ◇ (X0 ◇ X1)) = X1 ◇ (X2 ◇ (X0 ◇ X3)) := by
    first | exact superpose ef85 ef462 | exact superpose ef462 ef85
  have ef150211 :
      x ≠ ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))) ◇ (dr (y ◇ (dr y y)) ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇ (dl (dr y y) ((y ◇ y) ◇
      (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y)) := by
    first | exact superpose ef10722 ef304 | exact superpose ef304 ef10722
  have ef150212 :
      x ≠ ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))) ◇
      ((dl ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) y) ◇ (dl y y)) := by
    first | exact superpose ef709 ef150211 | exact superpose ef150211 ef709
  have ef150213 :
      x ≠ ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))) ◇ ((y ◇
      (dr (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) y)) ◇
      (dl y y)) := by
    first | exact superpose ef324 ef150212 | exact superpose ef150212 ef324
  have ef150214 :
      x ≠ ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))) ◇ ((y ◇
      ((dl y ((dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x)))) ◇
      (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))))) ◇
      x)) ◇ (dl y y)) := by
    first | exact superpose ef514 ef150213 | exact superpose ef150213 ef514
  have ef150215 :
      x ≠ ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))) ◇ ((y ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      (dr y (dl x (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x)))))))) ◇
      (dl y y)) := by
    first | exact superpose ef2948 ef150214 | exact superpose ef150214 ef2948
  have ef150216 :
      x ≠ ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇
      (dr ((dr y (dl x (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x)))))) ◇
      (dr x x)) ((y ◇ (dl (dr y y) (dl y y))) ◇ y)))) ◇ (dl y y)) := by
    first | exact superpose ef10722 ef150215 | exact superpose ef150215 ef10722
  have ef150217 :
      x ≠ ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇
      (dl x (dr y (dl x (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x)))))))))) ◇
      (dl y y)) := by
    first | exact superpose ef709 ef150216 | exact superpose ef150216 ef709
  have ef150218 :
      x ≠ ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇ (y ◇
      ((dl x (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇ x))))) ◇
      (dl y y)) := by
    first | exact superpose ef85 ef150217 | exact superpose ef150217 ef85
  have ef150219 :
      x ≠ ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇ (y ◇
      (((dl ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))) x) ◇ (dr y y)) ◇ x))))) ◇
      (dl y y)) := by
    first | exact superpose ef946 ef150218 | exact superpose ef150218 ef946
  have ef150220 :
      x ≠ ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇
      (dl x (y ◇ (dl ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))) x)))))) ◇
      (dl y y)) := by
    first | exact superpose ef1479 ef150219 | exact superpose ef150219 ef1479
  have ef150221 :
      x ≠ ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇
      (dl x (y ◇ ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x)) ◇ (dr (y ◇ y) x))))))) ◇
      (dl y y)) := by
    first | exact superpose ef324 ef150220 | exact superpose ef150220 ef324
  have ef150222 :
      x ≠ ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x)) ◇
      ((dr (dr (y ◇ y) x) y) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef220 ef150221 | exact superpose ef150221 ef220
  have ef150223 :
      x ≠ ((y ◇ y) ◇
      (((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇
      x) ◇
      (dl (dr y y) ((y ◇ y) ◇ (((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇
      ((((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x) ◇ ((((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ (dl (dr x x) ((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))) ◇ x)) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef517 ef150222 | exact superpose ef150222 ef517
  have ef150224 :
      x ≠ ((y ◇ y) ◇
      ((((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇
      (dr (x ◇ (dr x x)) ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ (dr (x ◇ (dr x x)) ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ (dr (x ◇ (dr x x)) ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))))) ◇
      y) ◇
      (((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇
      (dr (x ◇ (dr x x)) ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ (dr (x ◇ (dr x x)) ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ (dr (x ◇ (dr x x)) ((y ◇ (dl (dr y y) (dl y y))) ◇ y))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇
      (((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ (dr (x ◇ (dr x x)) ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ (dr (x ◇ (dr x x)) ((y ◇ (dl (dr y y) (dl y y))) ◇ y)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef10722 ef150223 | exact superpose ef150223 ef10722
  have ef150225 :
      x ≠ ((y ◇ y) ◇
      ((((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇
      ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇ (dl x x))))))) ◇
      y) ◇
      (((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇
      ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇
      (((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((dl ((y ◇ (dl (dr y y) (dl y y))) ◇ y) x) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef709 ef150224 | exact superpose ef150224 ef709
  have ef150226 :
      x ≠ ((y ◇ y) ◇
      ((((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇
      ((y ◇ (dr (y ◇ (dl (dr y y) (dl y y))) x)) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((y ◇ (dr (y ◇ (dl (dr y y) (dl y y))) x)) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((y ◇ (dr (y ◇ (dl (dr y y) (dl y y))) x)) ◇ (dl x x))))))) ◇
      y) ◇
      (((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇
      ((y ◇ (dr (y ◇ (dl (dr y y) (dl y y))) x)) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((y ◇ (dr (y ◇ (dl (dr y y) (dl y y))) x)) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((y ◇ (dr (y ◇ (dl (dr y y) (dl y y))) x)) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇
      ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((y ◇ (dr (y ◇ (dl (dr y y) (dl y y))) x)) ◇
      (((((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((y ◇ (dr (y ◇ (dl (dr y y) (dl y y))) x)) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ (dl (dr y y) (dl y y))) ◇ y) ◇ ((y ◇ (dl (dr y y) (dl y y))) ◇ y))) ◇ ((y ◇ (dr (y ◇ (dl (dr y y) (dl y y))) x)) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef324 ef150225 | exact superpose ef150225 ef324
  have ef150227 :
      x ≠ ((y ◇ y) ◇
      ((((((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇
      ((y ◇ (dr (y ◇ ((dl y (dr y y)) ◇ y)) x)) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ (dr (y ◇ ((dl y (dr y y)) ◇ y)) x)) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ (dr (y ◇ ((dl y (dr y y)) ◇ y)) x)) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇
      ((y ◇ (dr (y ◇ ((dl y (dr y y)) ◇ y)) x)) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ (dr (y ◇ ((dl y (dr y y)) ◇ y)) x)) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ (dr (y ◇ ((dl y (dr y y)) ◇ y)) x)) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇
      ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ (dr (y ◇ ((dl y (dr y y)) ◇ y)) x)) ◇
      (((((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ (dr (y ◇ ((dl y (dr y y)) ◇ y)) x)) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ (dr (y ◇ ((dl y (dr y y)) ◇ y)) x)) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef946 ef150226 | exact superpose ef150226 ef946
  have ef150228 :
      x ≠ ((y ◇ y) ◇
      ((((((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇
      ((y ◇ ((dr y (dl y (dr y y))) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (dl y (dr y y))) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (dl y (dr y y))) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇
      ((y ◇ ((dr y (dl y (dr y y))) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (dl y (dr y y))) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (dl y (dr y y))) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇
      ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (dl y (dr y y))) ◇ (dr x y))) ◇
      (((((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (dl y (dr y y))) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y) ◇ ((y ◇ ((dl y (dr y y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (dl y (dr y y))) ◇ (dr x y))) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef567 ef150227 | exact superpose ef150227 ef567
  have ef150229 :
      x ≠ ((y ◇ y) ◇
      ((((((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇
      ((y ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇
      ((y ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇
      ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr x y))) ◇
      (((((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr x y))) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef85 ef150228 | exact superpose ef150228 ef85
  have ef150230 :
      x ≠ ((y ◇ y) ◇
      ((((((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇
      ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y) ◇ ((y ◇ ((y ◇ (y ◇ y)) ◇ y)) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef38 ef150229 | exact superpose ef150229 ef38
  have ef150231 :
      x ≠ ((y ◇ y) ◇ ((((((x ◇ x) ◇ (dr (y ◇ ((y ◇ (y ◇ y)) ◇ y)) (dl ((y ◇ (y ◇ y)) ◇ y) y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (dr (y ◇ ((y ◇ (y ◇ y)) ◇ y)) (dl ((y ◇ (y ◇ y)) ◇ y) y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dr (y ◇ ((y ◇ (y ◇ y)) ◇ y)) (dl ((y ◇ (y ◇ y)) ◇ y) y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ (dr (y ◇ ((y ◇ (y ◇ y)) ◇ y)) (dl ((y ◇ (y ◇ y)) ◇ y) y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (dr (y ◇ ((y ◇ (y ◇ y)) ◇ y)) (dl ((y ◇ (y ◇ y)) ◇ y) y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dr (y ◇ ((y ◇ (y ◇ y)) ◇ y)) (dl ((y ◇ (y ◇ y)) ◇ y) y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (dr (y ◇ ((y ◇ (y ◇ y)) ◇ y)) (dl ((y ◇ (y ◇ y)) ◇ y) y))) ◇ ((y ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((x ◇ x) ◇ (dr (y ◇ ((y ◇ (y ◇ y)) ◇ y)) (dl ((y ◇ (y ◇ y)) ◇ y) y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dr (y ◇ ((y ◇ (y ◇ y)) ◇ y)) (dl ((y ◇ (y ◇ y)) ◇ y) y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef138 ef150230 | exact superpose ef150230 ef138
  have ef150232 :
      x ≠ ((y ◇ y) ◇ ((((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr (dl ((y ◇ (y ◇ y)) ◇ y) y) y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr (dl ((y ◇ (y ◇ y)) ◇ y) y) y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr (dl ((y ◇ (y ◇ y)) ◇ y) y) y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr (dl ((y ◇ (y ◇ y)) ◇ y) y) y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr (dl ((y ◇ (y ◇ y)) ◇ y) y) y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr (dl ((y ◇ (y ◇ y)) ◇ y) y) y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr (dl ((y ◇ (y ◇ y)) ◇ y) y) y))) ◇ ((y ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr (dl ((y ◇ (y ◇ y)) ◇ y) y) y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (dr (dl ((y ◇ (y ◇ y)) ◇ y) y) y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef567 ef150231 | exact superpose ef150231 ef567
  have ef150233 :
      x ≠ ((y ◇ y) ◇ ((((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dr y ((y ◇ (y ◇ y)) ◇ y))))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dr y ((y ◇ (y ◇ y)) ◇ y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dr y ((y ◇ (y ◇ y)) ◇ y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dr y ((y ◇ (y ◇ y)) ◇ y))))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dr y ((y ◇ (y ◇ y)) ◇ y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dr y ((y ◇ (y ◇ y)) ◇ y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dr y ((y ◇ (y ◇ y)) ◇ y))))) ◇ ((y ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dr y ((y ◇ (y ◇ y)) ◇ y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dr y ((y ◇ (y ◇ y)) ◇ y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef527 ef150232 | exact superpose ef150232 ef527
  have ef150234 :
      x ≠ ((y ◇ y) ◇ ((((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y)))))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y)))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y)))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y)))))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y)))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y)))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y)))))) ◇ ((y ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y)))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (y ◇ (y ◇ y)))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef38 ef150233 | exact superpose ef150233 ef38
  have ef150235 :
      x ≠ ((y ◇ y) ◇ ((((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dl (y ◇ y) y)))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dl (y ◇ y) y)))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dl (y ◇ y) y)))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dl (y ◇ y) y)))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dl (y ◇ y) y)))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dl (y ◇ y) y)))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dl (y ◇ y) y)))) ◇ ((y ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dl (y ◇ y) y)))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (dl (y ◇ y) y)))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef32 ef150234 | exact superpose ef150234 ef32
  have ef150236 :
      x ≠ ((y ◇ y) ◇ ((((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((dr y (y ◇ (y ◇ y))) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef324 ef150235 | exact superpose ef150235 ef324
  have ef150237 :
      x ≠ ((y ◇ y) ◇ ((((((x ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((x ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ (y ◇ (dr y y))))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef38 ef150236 | exact superpose ef150236 ef38
  have ef150238 :
      x ≠ ((y ◇ y) ◇ ((((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇
      ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)))) ◇
      (((dl y x) ◇ (y ◇ y)) ◇ x))))) ◇ (dl y y)) := by
    first | exact superpose ef32 ef150237 | exact superpose ef150237 ef32
  have ef150239 :
      x ≠ ((y ◇ y) ◇ ((((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇ ((y ◇ (((y ◇ y) ◇ y) ◇
      (dr (((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) (x ◇ x)))) ◇ (dl y y)) := by
    first | exact superpose ef10722 ef150238 | exact superpose ef150238 ef10722
  have ef150240 :
      x ≠ ((y ◇ y) ◇ ((((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇
      (((dl y (dr (((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) (x ◇ x))) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef10489 ef150239 | exact superpose ef150239 ef10489
  have ef150241 :
      x ≠ ((y ◇ y) ◇ ((((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y) ◇ (((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇
      ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x))) ◇ (((x ◇ x) ◇ (dl (y ◇ (dr y y)) ((y ◇ y) ◇ y))) ◇ ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef85 ef150240 | exact superpose ef150240 ef85
  have ef150242 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇
      (dr (((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) ◇ (y ◇ (dr y y))) (x ◇ x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (dr (((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) ◇ (y ◇ (dr y y))) (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ (dr (((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) ◇ (y ◇ (dr y y))) (x ◇ x))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇
      (dr (((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) ◇ (y ◇ (dr y y))) (x ◇ x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (dr (((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) ◇ (y ◇ (dr y y))) (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ (dr (((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) ◇ (y ◇ (dr y y))) (x ◇ x))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((y ◇ y) ◇ y) ◇ (dr (((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) ◇ (y ◇ (dr y y))) (x ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ (dr (((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) ◇ (y ◇ (dr y y))) (x ◇ x)))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef10722 ef150241 | exact superpose ef150241 ef10722
  have ef150243 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇
      ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (dr (x ◇ x) (dr y y)))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (dr (x ◇ x) (dr y y)))) ◇ (((y ◇ y) ◇ y) ◇ ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (dr (x ◇ x) (dr y y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇
      ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (dr (x ◇ x) (dr y y)))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (dr (x ◇ x) (dr y y)))) ◇ (((y ◇ y) ◇ y) ◇ ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (dr (x ◇ x) (dr y y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((y ◇ y) ◇ y) ◇ ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (dr (x ◇ x) (dr y y)))) ◇ (((y ◇ y) ◇ y) ◇ ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (dr (x ◇ x) (dr y y))))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef567 ef150242 | exact superpose ef150242 ef567
  have ef150244 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇
      ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇ (((y ◇ y) ◇ y) ◇ ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (y ◇ ((x ◇ x) ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇
      ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇ (((y ◇ y) ◇ y) ◇ ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (y ◇ ((x ◇ x) ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((y ◇ y) ◇ y) ◇ ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇ (((y ◇ y) ◇ y) ◇ ((dr ((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (dl x x)) y) ◇ (y ◇ ((x ◇ x) ◇ y))))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef63 ef150243 | exact superpose ef150243 ef63
  have ef150245 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇
      (((dl y ((dl x x) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (((dl y ((dl x x) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇ (((y ◇ y) ◇ y) ◇ (((dl y ((dl x x) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (y ◇ ((x ◇ x) ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇
      (((dl y ((dl x x) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (((dl y ((dl x x) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇ (((y ◇ y) ◇ y) ◇ (((dl y ((dl x x) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (y ◇ ((x ◇ x) ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((y ◇ y) ◇ y) ◇ (((dl y ((dl x x) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇ (((y ◇ y) ◇ y) ◇ (((dl y ((dl x x) ◇ y)) ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇ (y ◇ ((x ◇ x) ◇ y))))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef514 ef150244 | exact superpose ef150244 ef514
  have ef150246 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇
      ((dl (dr x y) (((dl x x) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ ((dl (dr x y) (((dl x x) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇ (((y ◇ y) ◇ y) ◇ ((dl (dr x y) (((dl x x) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((x ◇ x) ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇
      ((dl (dr x y) (((dl x x) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ ((dl (dr x y) (((dl x x) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇ (((y ◇ y) ◇ y) ◇ ((dl (dr x y) (((dl x x) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((x ◇ x) ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((y ◇ y) ◇ y) ◇ ((dl (dr x y) (((dl x x) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((x ◇ x) ◇ y)))) ◇ (((y ◇ y) ◇ y) ◇ ((dl (dr x y) (((dl x x) ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ (y ◇ ((x ◇ x) ◇ y))))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef147 ef150245 | exact superpose ef150245 ef147
  have ef150247 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (dr (dr x y) (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y))))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (dr (dr x y) (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y))))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (dr (dr x y) (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y))))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (dr (dr x y) (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y))))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (dr (dr x y) (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y))))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (dr (dr x y) (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y))))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (dr (dr x y) (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y))))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (dr (dr x y) (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y)))))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef2948 ef150246 | exact superpose ef150246 ef2948
  have ef150248 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ ((dl (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y)) y) ◇ x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ ((dl (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y)) y) ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ ((dl (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y)) y) ◇ x))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ ((dl (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y)) y) ◇ x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ ((dl (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y)) y) ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ ((dl (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y)) y) ◇ x))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ ((dl (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y)) y) ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ ((dl (dl (y ◇ ((x ◇ x) ◇ y)) ((dl x x) ◇ y)) y) ◇ x)))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef517 ef150247 | exact superpose ef150247 ef517
  have ef150249 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((dl x x) ◇ y)) ◇ x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((dl x x) ◇ y)) ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((dl x x) ◇ y)) ◇ x))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((y ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((dl x x) ◇ y)) ◇ x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((dl x x) ◇ y)) ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((dl x x) ◇ y)) ◇ x))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((dl x x) ◇ y)) ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((dl x x) ◇ y)) ◇ x)))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef137 ef150248 | exact superpose ef150248 ef137
  have ef150250 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (((dr y (x ◇ x)) ◇ ((dl x x) ◇ y)) ◇ x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((dr y (x ◇ x)) ◇ ((dl x x) ◇ y)) ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((dr y (x ◇ x)) ◇ ((dl x x) ◇ y)) ◇ x))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((dr y (x ◇ x)) ◇ ((dl x x) ◇ y)) ◇ x))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((dr y (x ◇ x)) ◇ ((dl x x) ◇ y)) ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((dr y (x ◇ x)) ◇ ((dl x x) ◇ y)) ◇ x))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((dr y (x ◇ x)) ◇ ((dl x x) ◇ y)) ◇ x))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (((dr y (x ◇ x)) ◇ ((dl x x) ◇ y)) ◇ x)))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef25 ef150249 | exact superpose ef150249 ef25
  have ef150251 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇
      (((y ◇ y) ◇ y) ◇ (y ◇ ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x))))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (y ◇ ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x))))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (y ◇ ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x))))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (y ◇ ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x))))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (y ◇ ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x))))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (y ◇ ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x))))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (y ◇ ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x))))) ◇ (((y ◇ y) ◇ y) ◇ (((y ◇ y) ◇ y) ◇ (y ◇ ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)))))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef410 ef150250 | exact superpose ef150250 ef410
  have ef150252 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef32 ef150251 | exact superpose ef150251 ef32
  have ef150253 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dr ((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x))) ((y ◇ y) ◇ y)))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dr ((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x))) ((y ◇ y) ◇ y)))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((y ◇ y) ◇ (dr ((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x))) ((y ◇ y) ◇ y))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef10722 ef150252 | exact superpose ef150252 ef10722
  have ef150254 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (dr ((y ◇ y) ◇ y) (dl ((dl x x) ◇ y) x))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (dr ((y ◇ y) ◇ y) (dl ((dl x x) ◇ y) x))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (dr ((y ◇ y) ◇ y) (dl ((dl x x) ◇ y) x)))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef567 ef150253 | exact superpose ef150253 ef567
  have ef150255 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ ((dl (dl ((dl x x) ◇ y) x) (y ◇ y)) ◇ y)))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ ((dl (dl ((dl x x) ◇ y) x) (y ◇ y)) ◇ y)))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ ((dl (dl ((dl x x) ◇ y) x) (y ◇ y)) ◇ y))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef514 ef150254 | exact superpose ef150254 ef514
  have ef150256 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (dr (dl ((dl x x) ◇ y) x) (dl y y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (dr (dl ((dl x x) ◇ y) x) (dl y y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (dr (dl ((dl x x) ◇ y) x) (dl y y))))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef2948 ef150255 | exact superpose ef150255 ef2948
  have ef150257 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (x ◇ (dr (dl y y) ((dl x x) ◇ y))))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (x ◇ (dr (dl y y) ((dl x x) ◇ y))))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (x ◇ (dr (dl y y) ((dl x x) ◇ y)))))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef527 ef150256 | exact superpose ef150256 ef527
  have ef150258 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (x ◇ ((y ◇ (dl y y)) ◇ (dl x x))))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (x ◇ ((y ◇ (dl y y)) ◇ (dl x x))))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (x ◇ ((y ◇ (dl y y)) ◇ (dl x x)))))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef38 ef150257 | exact superpose ef150257 ef38
  have ef150259 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (x ◇ (y ◇ (dr ((dl x x) ◇ y) y))))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (x ◇ (y ◇ (dr ((dl x x) ◇ y) y))))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (x ◇ (y ◇ (dr ((dl x x) ◇ y) y)))))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef10722 ef150258 | exact superpose ef150258 ef10722
  have ef150260 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (x ◇ (y ◇ (dl x x))))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (x ◇ (y ◇ (dl x x))))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((y ◇ y) ◇ ((dr (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) (x ◇ x)) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef15 ef150259 | exact superpose ef150259 ef15
  have ef150261 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (((dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))) ◇ y) ◇ (y ◇ (x ◇ (y ◇ (dl x x))))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (((dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))) ◇ y) ◇ (y ◇ (x ◇ (y ◇ (dl x x))))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((y ◇ y) ◇ (((dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))) ◇ y) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef514 ef150260 | exact superpose ef150260 ef514
  have ef150262 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ◇ (((dl y x) ◇ (y ◇ y)) ◇ x))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef32 ef150261 | exact superpose ef150261 ef32
  have ef150263 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))) ◇ (dr ((((dl y x) ◇ (y ◇ y)) ◇ x) ◇ (x ◇ (y ◇ (dl x x)))) (y ◇ y)))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef10722 ef150262 | exact superpose ef150262 ef10722
  have ef150264 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ (dr (x ◇ x) (dl (dr ((((dl y x) ◇ (y ◇ y)) ◇ x) ◇ (x ◇ (y ◇ (dl x x)))) (y ◇ y)) (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef2948 ef150263 | exact superpose ef150263 ef2948
  have ef150265 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ (dr (x ◇ x) ((dl (y ◇ y) (dr ((((dl y x) ◇ (y ◇ y)) ◇ x) ◇ (x ◇ (y ◇ (dl x x)))) (y ◇ y))) ◇ ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef946 ef150264 | exact superpose ef150264 ef946
  have ef150266 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) ◇ (x ◇ x)) ◇ (dl (y ◇ y) (dr ((((dl y x) ◇ (y ◇ y)) ◇ x) ◇ (x ◇ (y ◇ (dl x x)))) (y ◇ y)))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef38 ef150265 | exact superpose ef150265 ef38
  have ef150267 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) ◇ (x ◇ x)) ◇ (((((dl y x) ◇ (y ◇ y)) ◇ x) ◇ (x ◇ (y ◇ (dl x x)))) ◇ ((y ◇ y) ◇ (y ◇ y)))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef85 ef150266 | exact superpose ef150266 ef85
  have ef150268 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) ◇ (x ◇ x)) ◇ (((((dl y x) ◇ (y ◇ y)) ◇ x) ◇ (x ◇ (y ◇ (dl x x)))) ◇ (dl y y))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef32 ef150267 | exact superpose ef150267 ef32
  have ef150269 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) ◇ (x ◇ x)) ◇ ((dl (y ◇ (dl x x)) ((dl y x) ◇ (y ◇ y))) ◇ (dl y y))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef32 ef150268 | exact superpose ef150268 ef32
  have ef150270 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (dr (y ◇ (dl x x)) (dl (dl y y) (dl y x))))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef2948 ef150269 | exact superpose ef150269 ef2948
  have ef150271 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (dr (y ◇ (dl x x)) ((dl x (dl y y)) ◇ y)))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef946 ef150270 | exact superpose ef150270 ef946
  have ef150272 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ (y ◇ (dl x x))) ◇ (dl x (dl y y))))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef38 ef150271 | exact superpose ef150271 ef38
  have ef150273 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ (y ◇ (dl x x))) ◇ ((dl y x) ◇ y)))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef946 ef150272 | exact superpose ef150272 ef946
  have ef150274 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (x ◇ ((y ◇ (dl x x)) ◇ y)))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef444 ef150273 | exact superpose ef150273 ef444
  have ef150275 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ (x ◇ (x ◇ (dr (y ◇ x) y))))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef10722 ef150274 | exact superpose ef150274 ef10722
  have ef150276 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((x ◇ (dr ((x ◇ x) ◇ ((dl x x) ◇ y)) (x ◇ x))) ◇ ((y ◇ y) ◇ (x ◇ (x ◇ (dr (y ◇ x) y))))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef10722 ef150275 | exact superpose ef150275 ef10722
  have ef150277 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((x ◇ ((dr (x ◇ x) (dl x x)) ◇ (dr (x ◇ x) y))) ◇ ((y ◇ y) ◇ (x ◇ (x ◇ (dr (y ◇ x) y))))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef567 ef150276 | exact superpose ef150276 ef567
  have ef150278 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((x ◇ ((dr x x) ◇ (dr (x ◇ x) y))) ◇ ((y ◇ y) ◇ (x ◇ (x ◇ (dr (y ◇ x) y))))))) ◇
      (y ◇ (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef647 ef150277 | exact superpose ef150277 ef647
  have ef150279 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ ((x ◇ (dl (dr x x) y)) ◇ ((y ◇ y) ◇ (x ◇ (x ◇ (dr (y ◇ x) y))))))) ◇ (y ◇
      (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef1453 ef150278 | exact superpose ef150278 ef1453
  have ef150280 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      ((y ◇ y) ◇ (y ◇ (dr (((y ◇ y) ◇ (x ◇ (x ◇ (dr (y ◇ x) y)))) ◇ (dr x x)) x)))) ◇ (y ◇
      (dr y y))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef10722 ef150279 | exact superpose ef150279 ef10722
  have ef150281 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((((y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) ◇
      (dl (dr (((y ◇ y) ◇ (x ◇ (x ◇ (dr (y ◇ x) y)))) ◇ (dr x x)) x) y)) ◇ (y ◇ (dr y y))) ◇ ((x ◇
      x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef32 ef150280 | exact superpose ef150280 ef32
  have ef150282 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((y ◇
      (dr ((y ◇ (dr y y)) ◇ (dr (((y ◇ y) ◇ (x ◇ (x ◇ (dr (y ◇ x) y)))) ◇ (dr x x)) x)) (y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))))) ◇
      ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef10722 ef150281 | exact superpose ef150281 ef10722
  have ef150283 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((y ◇
      ((dl (y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) (((y ◇ y) ◇ (x ◇ (x ◇ (dr (y ◇ x) y)))) ◇ (dr x x))) ◇
      (dl x (y ◇ (dr y y))))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef709 ef150282 | exact superpose ef150282 ef709
  have ef150284 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((y ◇ ((dr x x) ◇
      (dr (y ◇ ((((y ◇ y) ◇ y) ◇ y) ◇ (dr x y))) (dl (dl x (y ◇ (dr y y))) ((y ◇ y) ◇ (x ◇ (x ◇ (dr (y ◇ x) y)))))))) ◇
      ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef2948 ef150283 | exact superpose ef150283 ef2948
  have ef150285 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((y ◇ ((dr x x) ◇
      ((dr y (((y ◇ y) ◇ y) ◇ y)) ◇ (dr (dl (dl x (y ◇ (dr y y))) ((y ◇ y) ◇ (x ◇ (x ◇ (dr (y ◇ x) y))))) (dr x y))))) ◇
      ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef567 ef150284 | exact superpose ef150284 ef567
  have ef150286 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((y ◇ ((dr x x) ◇
      ((dr y (((y ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((dl (dl x (y ◇ (dr y y))) ((y ◇ y) ◇ (x ◇ (x ◇ (dr (y ◇ x) y))))) ◇ x))))) ◇
      ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef63 ef150285 | exact superpose ef150285 ef63
  have ef150287 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((y ◇ ((dr x x) ◇
      ((dr y (((y ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ (dr (dl x (y ◇ (dr y y))) (dl x (y ◇ y)))))))) ◇
      ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef2948 ef150286 | exact superpose ef150286 ef2948
  have ef150288 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((y ◇ ((dr x x) ◇
      ((dr y (((y ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ (dr (dl x (y ◇ y)) x))))))) ◇
      ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef527 ef150287 | exact superpose ef150287 ef527
  have ef150289 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((y ◇ ((dr x x) ◇
      ((dr y (((y ◇ y) ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef527 ef150288 | exact superpose ef150288 ef527
  have ef150290 :
      x ≠ ((y ◇ y) ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y) ◇ (((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr y y) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ◇
      y))) ◇ ((((y ◇ ((dr x x) ◇
      (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef38 ef150289 | exact superpose ef150289 ef38
  have ef150291 :
      x ≠ ((y ◇ y) ◇ ((((y ◇ y) ◇ ((y ◇ y) ◇
      (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))) ◇
      (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))))) ◇ (((y ◇
      y) ◇ ((y ◇ y) ◇
      (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))) ◇
      (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))))))) ◇
      ((((y ◇ ((dr x x) ◇
      (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef10722 ef150290 | exact superpose ef150290 ef10722
  have ef150292 :
      x ≠ ((dl (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇
      (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (((y ◇ y) ◇ ((y ◇ y) ◇
      (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))) ◇
      (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))))) ◇ ((y ◇
      y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇
      (y ◇ y)))))) ◇ ((((y ◇ ((dr x x) ◇
      (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef10489 ef150291 | exact superpose ef150291 ef10489
  have ef150293 :
      x ≠ ((dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) ◇
      (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇
      (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇
      (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇
      y) ◇ ((y ◇ y) ◇
      (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))))))) ◇
      ((((y ◇ ((dr x x) ◇
      (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)) := by
    first | exact superpose ef2948 ef150292 | exact superpose ef150292 ef2948
  have ef150294 :
      x ≠ (y ◇ (dr y y)) ◇ ((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇
      (dl (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇
      (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇
      (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇
      ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ((((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)))) := by
    first | exact superpose ef410 ef150293 | exact superpose ef150293 ef410
  have ef150295 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇
      (dr ((dl (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ((((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇
      (dl y y))) ◇ ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x))) ((y ◇ y) ◇ y))) := by
    first | exact superpose ef10722 ef150294 | exact superpose ef150294 ef10722
  have ef150296 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇
      ((dr (dl (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ((((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇
      (dl y y))) (x ◇ x)) ◇ (dr ((y ◇ y) ◇ y) (dl ((dl x x) ◇ y) x)))) := by
    first | exact superpose ef567 ef150295 | exact superpose ef150295 ef567
  have ef150297 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇
      ((dr (dl (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ((((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇
      (dl y y))) (x ◇ x)) ◇ ((dl (dl ((dl x x) ◇ y) x) (y ◇ y)) ◇ y))) := by
    first | exact superpose ef514 ef150296 | exact superpose ef150296 ef514
  have ef150298 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇
      ((dr (dl (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ((((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇
      (dl y y))) (x ◇ x)) ◇ (y ◇ (dr (dl ((dl x x) ◇ y) x) (dl y y))))) := by
    first | exact superpose ef2948 ef150297 | exact superpose ef150297 ef2948
  have ef150299 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇
      ((dr (dl (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ((((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇
      (dl y y))) (x ◇ x)) ◇ (y ◇ (x ◇ (dr (dl y y) ((dl x x) ◇ y)))))) := by
    first | exact superpose ef527 ef150298 | exact superpose ef150298 ef527
  have ef150300 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇
      ((dr (dl (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ((((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇
      (dl y y))) (x ◇ x)) ◇ (y ◇ (x ◇ ((y ◇ (dl y y)) ◇ (dl x x)))))) := by
    first | exact superpose ef38 ef150299 | exact superpose ef150299 ef38
  have ef150301 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇
      ((dr (dl (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ((((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇
      (dl y y))) (x ◇ x)) ◇ (y ◇ (x ◇ (y ◇ (dr ((dl x x) ◇ y) y)))))) := by
    first | exact superpose ef10722 ef150300 | exact superpose ef150300 ef10722
  have ef150302 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇
      ((dr (dl (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ((((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇
      (dl y y))) (x ◇ x)) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef15 ef150301 | exact superpose ef150301 ef15
  have ef150303 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (((x ◇
      (dl (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ((((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇ ((x ◇ x) ◇ y)) ◇ y) ◇ (dl y y)))) ◇
      x) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef38 ef150302 | exact superpose ef150302 ef38
  have ef150304 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇
      ((((((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇ ((x ◇ x) ◇ y)) ◇
      y) ◇ (dl y y)) ◇ (dr (x ◇
      (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))))))) x)) ◇
      (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef10722 ef150303 | exact superpose ef150303 ef10722
  have ef150305 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇
      (dr ((dr (x ◇ (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))))))) x) ◇
      y) (((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇ ((x ◇ x) ◇ y)) ◇
      y))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef10722 ef150304 | exact superpose ef150304 ef10722
  have ef150306 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      ((dr (x ◇ (dr (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))) (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))))))) x) ◇ y)) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef38 ef150305 | exact superpose ef150305 ef38
  have ef150307 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (((dl x (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))))) ◇ (dl (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))))) x)) ◇ y)) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef709 ef150306 | exact superpose ef150306 ef709
  have ef150308 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ (dr (y ◇ (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) (dl x (dr (y ◇ (dr y y)) (((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)))))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef10722 ef150307 | exact superpose ef150307 ef10722
  have ef150309 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ (dr (y ◇ (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))))))) ((y ◇ (dr y y)) ◇ ((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef85 ef150308 | exact superpose ef150308 ef85
  have ef150310 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ (dl ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))) ((y ◇ y) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef38 ef150309 | exact superpose ef150309 ef38
  have ef150311 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)))) (y ◇ y)) ◇ ((y ◇ y) ◇ (dl (x ◇ (y ◇ (dl x x))) (dl (x ◇ x) ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef220 ef150310 | exact superpose ef150310 ef220
  have ef150312 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr ((dl ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)) (x ◇ (y ◇ (dl x x)))) ◇ (x ◇ x)) (y ◇ y)) ◇ ((y ◇ y) ◇ ((dl ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)) (x ◇ (y ◇ (dl x x)))) ◇ (x ◇ x))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef946 ef150311 | exact superpose ef150311 ef946
  have ef150313 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr ((y ◇ (dl x x)) ◇ (dr ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)) (dl (x ◇ x) x))) (y ◇ y)) ◇ ((y ◇ y) ◇ ((y ◇ (dl x x)) ◇ (dr ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)) (dl (x ◇ x) x)))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef2948 ef150312 | exact superpose ef150312 ef2948
  have ef150314 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (x ◇ (dr ((dr ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)) (dl (x ◇ x) x)) ◇ x) y)) (y ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ (dr ((dr ((dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) ◇ (y ◇ y)) (dl (x ◇ x) x)) ◇ x) y))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef10722 ef150313 | exact superpose ef150313 ef10722
  have ef150315 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (x ◇ (dr (((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (dr (dl (x ◇ x) x) y)) ◇ x) y)) (y ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ (dr (((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (dr (dl (x ◇ x) x) y)) ◇ x) y))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef567 ef150314 | exact superpose ef150314 ef567
  have ef150316 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (x ◇ ((dl y (x ◇ (dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y))) ◇ (dr (dl (x ◇ x) x) y))) (y ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ ((dl y (x ◇ (dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y))) ◇ (dr (dl (x ◇ x) x) y)))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef514 ef150315 | exact superpose ef150315 ef514
  have ef150317 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (x ◇ ((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (dr y (dl (dr (dl (x ◇ x) x) y) x)))) (y ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ ((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (dr y (dl (dr (dl (x ◇ x) x) y) x))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef2948 ef150316 | exact superpose ef150316 ef2948
  have ef150318 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (x ◇ ((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (dr y (dl (x ◇ (dr y (x ◇ x))) x)))) (y ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ ((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (dr y (dl (x ◇ (dr y (x ◇ x))) x))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef527 ef150317 | exact superpose ef150317 ef527
  have ef150319 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (x ◇ ((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (dr y ((dr y (x ◇ x)) ◇ (dr x x))))) (y ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ ((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (dr y ((dr y (x ◇ x)) ◇ (dr x x)))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef324 ef150318 | exact superpose ef150318 ef324
  have ef150320 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (x ◇ ((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (((dr x x) ◇ y) ◇ (dr y (x ◇ x))))) (y ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ ((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (((dr x x) ◇ y) ◇ (dr y (x ◇ x)))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef38 ef150319 | exact superpose ef150319 ef38
  have ef150321 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (x ◇ ((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (x ◇ (x ◇ (dl y (dr y (x ◇ x))))))) (y ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ ((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (x ◇ (x ◇ (dl y (dr y (x ◇ x)))))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef410 ef150320 | exact superpose ef150320 ef410
  have ef150322 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (x ◇ ((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))) (y ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ ((dr (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y)) y) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef85 ef150321 | exact superpose ef150321 ef85
  have ef150323 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (x ◇ (((y ◇ y) ◇ (dr y ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))) (y ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (dr y ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef527 ef150322 | exact superpose ef150322 ef527
  have ef150324 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (dl ((dl x x) ◇ y) x)) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (x ◇ (((y ◇ y) ◇ (((dl ((dl x x) ◇ y) x) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))) (y ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((dl ((dl x x) ◇ y) x) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef38 ef150323 | exact superpose ef150323 ef38
  have ef150325 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (dr (dl x x) x))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (x ◇ (((y ◇ y) ◇ (((y ◇ (dr (dl x x) x)) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))) (y ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (dr (dl x x) x)) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef324 ef150324 | exact superpose ef150324 ef324
  have ef150326 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x)))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ ((dr (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))) (y ◇ y)) ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef527 ef150325 | exact superpose ef150325 ef527
  have ef150327 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x)))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ (((dr x ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x)))) ◇ (dr (y ◇ y) (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))) ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef567 ef150326 | exact superpose ef150326 ef567
  have ef150328 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x)))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (dl (dr (y ◇ y) (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))) ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef410 ef150327 | exact superpose ef150327 ef410
  have ef150329 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x)))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ ((dr (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))) (y ◇ y)) ◇ (dr (y ◇ y) (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef220 ef150328 | exact superpose ef150328 ef220
  have ef150330 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x)))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ ((dr (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))) (y ◇ y)) ◇ (((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ (y ◇ y)) ◇ x)))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef38 ef150329 | exact superpose ef150329 ef38
  have ef150331 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x)))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (dr (dr (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))) (y ◇ y)) ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ (y ◇ y)))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef25 ef150330 | exact superpose ef150330 ef25
  have ef150332 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x)))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ (dr (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))) (y ◇ y))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef38 ef150331 | exact superpose ef150331 ef38
  have ef150333 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x)))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((dr ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) x) ◇ (dr (y ◇ y) (x ◇ (y ◇ ((x ◇ x) ◇ y)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef567 ef150332 | exact superpose ef150332 ef567
  have ef150334 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x)))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((dr ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) x) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ (y ◇ y)) ◇ x))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef38 ef150333 | exact superpose ef150333 ef38
  have ef150335 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x)))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ (((dr (y ◇ y) ((y ◇ (x ◇ (dr x x))) ◇ y)) ◇ (dr x (x ◇ x))) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ (y ◇ y)) ◇ x))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef567 ef150334 | exact superpose ef150334 ef567
  have ef150336 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x)))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (dl (dr x (x ◇ x)) (((y ◇ ((x ◇ x) ◇ y)) ◇ (y ◇ y)) ◇ x))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef410 ef150335 | exact superpose ef150335 ef410
  have ef150337 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x)))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ (dr x (x ◇ x))))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef146 ef150336 | exact superpose ef150336 ef146
  have ef150338 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((((y ◇ y) ◇ y) ◇ (dl ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x)))) (y ◇ y))) ◇ x) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef38 ef150337 | exact superpose ef150337 ef38
  have ef150339 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((y ◇ y) ◇ (dr (x ◇ ((x ◇ x) ◇ (y ◇ (x ◇ (dr x x))))) ((y ◇ y) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef10722 ef150338 | exact superpose ef150338 ef10722
  have ef150340 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((y ◇ y) ◇ ((dr x (x ◇ x)) ◇ (dr ((y ◇ y) ◇ y) (y ◇ (x ◇ (dr x x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef567 ef150339 | exact superpose ef150339 ef567
  have ef150341 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((y ◇ y) ◇ ((dr x (x ◇ x)) ◇ ((dl (y ◇ (x ◇ (dr x x))) (y ◇ y)) ◇ y))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef514 ef150340 | exact superpose ef150340 ef514
  have ef150342 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((y ◇ y) ◇ ((dr x (x ◇ x)) ◇ (y ◇ (dr (y ◇ (x ◇ (dr x x))) (dl y y))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef2948 ef150341 | exact superpose ef150341 ef2948
  have ef150343 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((y ◇ y) ◇ ((dr x (x ◇ x)) ◇ (y ◇ (dr y (x ◇ (dr x x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef647 ef150342 | exact superpose ef150342 ef647
  have ef150344 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((y ◇ y) ◇ ((dr x (x ◇ x)) ◇ (y ◇ (((dr x x) ◇ y) ◇ x)))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef38 ef150343 | exact superpose ef150343 ef38
  have ef150345 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((y ◇ y) ◇ ((dr x (x ◇ x)) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef410 ef150344 | exact superpose ef150344 ef410
  have ef150346 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((y ◇ ((y ◇
      (x ◇ ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) ◇
      ((y ◇ ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)))) ◇ (y ◇ (x ◇ (y ◇ (dl x x)))))) := by
    first | exact superpose ef38 ef150345 | exact superpose ef150345 ef38
  have ef150427 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (dr ((y ◇
      ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      ((x ◇ x) ◇ y)) y))) := by
    first | exact superpose ef1492 ef150346 | exact superpose ef150346 ef1492
  have ef150438 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ ((dr (y ◇
      ((dr x x) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) (x ◇
      x)) ◇ (dr y y)))) := by
    first | exact superpose ef567 ef150427 | exact superpose ef150427 ef567
  have ef150477 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (((dr y (dr x x)) ◇
      (dr (x ◇ x) (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))) ◇
      (dr y y)))) := by
    first | exact superpose ef567 ef150438 | exact superpose ef150438 ef567
  have ef150511 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (y ◇ ((dr x x) ◇
      (dl (dr (x ◇ x) (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x))))))) (dr y y)))))) := by
    first | exact superpose ef410 ef150477 | exact superpose ef150477 ef410
  have ef150543 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (y ◇ ((dr x x) ◇ (y ◇
      (y ◇ (dr (x ◇ x) (((y ◇ y) ◇ ((y ◇ y) ◇ y)) ◇ (y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x))))))))))))) := by
    first | exact superpose ef85 ef150511 | exact superpose ef150511 ef85
  have ef150569 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (y ◇ ((dr x x) ◇ (y ◇
      (y ◇ (((y ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x))))) ◇ (x ◇ x)) ◇ ((y ◇ y) ◇ ((y ◇ y) ◇ y))))))))) := by
    first | exact superpose ef38 ef150543 | exact superpose ef150543 ef38
  have ef150592 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (y ◇ ((dr x x) ◇ (y ◇
      ((dl (x ◇ x) ((y ◇ y) ◇ ((y ◇ y) ◇ y))) ◇ ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))))))))) := by
    first | exact superpose ef10489 ef150569 | exact superpose ef150569 ef10489
  have ef150615 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (y ◇ ((dr x x) ◇ (y ◇
      (((y ◇ y) ◇ y) ◇ (dr (x ◇ x) (dl ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))) (y ◇ y))))))))) := by
    first | exact superpose ef2948 ef150592 | exact superpose ef150592 ef2948
  have ef150638 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (y ◇ ((dr x x) ◇
      ((dl y (dr (x ◇ x) (dl ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))) (y ◇ y)))) ◇
      y))))) := by
    first | exact superpose ef10489 ef150615 | exact superpose ef150615 ef10489
  have ef150657 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇
      (dr (dr x x) (dl y (dr (x ◇ x) (dl ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))) (y ◇ y))))))) := by
    first | exact superpose ef25 ef150638 | exact superpose ef150638 ef25
  have ef150676 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇
      ((dl (dl y (dr (x ◇ x) (dl ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))) (y ◇ y)))) x) ◇
      x))) := by
    first | exact superpose ef517 ef150657 | exact superpose ef150657 ef517
  have ef150693 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (((x ◇ y) ◇
      (dr (x ◇ x) (dl ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))) (y ◇ y)))) ◇
      x))) := by
    first | exact superpose ef137 ef150676 | exact superpose ef150676 ef137
  have ef150710 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇
      ((((dl ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))) (y ◇ y)) ◇ y) ◇
      x) ◇ x))) := by
    first | exact superpose ef1502 ef150693 | exact superpose ef150693 ef1502
  have ef150726 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (((y ◇
      (dr ((x ◇ (x ◇ (dr (y ◇ x) y))) ◇ ((y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (dr x x)))) (dl y y))) ◇ x) ◇
      x))) := by
    first | exact superpose ef2948 ef150710 | exact superpose ef150710 ef2948
  have ef150741 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (((y ◇
      ((dr (x ◇ (x ◇ (dr (y ◇ x) y))) (y ◇ (dr y y))) ◇ (dr (dl y y) ((y ◇ y) ◇ (dr x x))))) ◇ x) ◇
      x))) := by
    first | exact superpose ef567 ef150726 | exact superpose ef150726 ef567
  have ef150756 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (((y ◇
      ((dr (x ◇ (x ◇ (dr (y ◇ x) y))) (y ◇ (dr y y))) ◇ (((dr x x) ◇ (dl y y)) ◇ (y ◇ y)))) ◇ x) ◇
      x))) := by
    first | exact superpose ef38 ef150741 | exact superpose ef150741 ef38
  have ef150771 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (((y ◇
      ((dr (x ◇ (x ◇ (dr (y ◇ x) y))) (y ◇ (dr y y))) ◇ (y ◇ (dr ((y ◇ y) ◇ y) (dr x x))))) ◇ x) ◇
      x))) := by
    first | exact superpose ef10722 ef150756 | exact superpose ef150756 ef10722
  have ef150786 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (((y ◇
      ((dr (x ◇ (x ◇ (dr (y ◇ x) y))) (y ◇ (dr y y))) ◇ (y ◇ ((dl (dr x x) (y ◇ y)) ◇ y)))) ◇ x) ◇
      x))) := by
    first | exact superpose ef514 ef150771 | exact superpose ef150771 ef514
  have ef150800 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (((y ◇
      ((dr (x ◇ (x ◇ (dr (y ◇ x) y))) (y ◇ (dr y y))) ◇ (y ◇ (y ◇ (dr (dr x x) (dl y y)))))) ◇ x) ◇
      x))) := by
    first | exact superpose ef2948 ef150786 | exact superpose ef150786 ef2948
  have ef150814 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (((y ◇
      ((dr (x ◇ (x ◇ (dr (y ◇ x) y))) (y ◇ (dr y y))) ◇ (y ◇ (y ◇ ((dl (dl y y) x) ◇ x))))) ◇ x) ◇
      x))) := by
    first | exact superpose ef517 ef150800 | exact superpose ef150800 ef517
  have ef150824 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (((y ◇
      ((dr (x ◇ (x ◇ (dr (y ◇ x) y))) (y ◇ (dr y y))) ◇ (y ◇ (y ◇ (((x ◇ y) ◇ y) ◇ x))))) ◇ x) ◇
      x))) := by
    first | exact superpose ef137 ef150814 | exact superpose ef150814 ef137
  have ef150833 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (((y ◇
      (((dr x x) ◇ (dr (y ◇ (dr y y)) (dr (y ◇ x) y))) ◇ (y ◇ (y ◇ (((x ◇ y) ◇ y) ◇ x))))) ◇ x) ◇
      x))) := by
    first | exact superpose ef567 ef150824 | exact superpose ef150824 ef567
  have ef150842 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (((y ◇
      (x ◇ (x ◇ (dl (dr (y ◇ (dr y y)) (dr (y ◇ x) y)) (y ◇ (y ◇ (((x ◇ y) ◇ y) ◇ x))))))) ◇ x) ◇
      x))) := by
    first | exact superpose ef410 ef150833 | exact superpose ef150833 ef410
  have ef150851 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇
      ((dl (dr (dl (dr (y ◇ (dr y y)) (dr (y ◇ x) y)) (y ◇ (y ◇ (((x ◇ y) ◇ y) ◇ x)))) x) y) ◇
      x))) := by
    first | exact superpose ef221 ef150842 | exact superpose ef150842 ef221
  have ef150860 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (x ◇ ((dr x y) ◇
      (dl (dr (y ◇ (dr y y)) (dr (y ◇ x) y)) (y ◇ (y ◇ (((x ◇ y) ◇ y) ◇ x)))))))) := by
    first | exact superpose ef1285 ef150851 | exact superpose ef150851 ef1285
  have ef150869 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (x ◇ ((dr x y) ◇ (y ◇
      ((dr (((x ◇ y) ◇ y) ◇ x) y) ◇ (dr (y ◇ (dr y y)) (dr (y ◇ x) y)))))))) := by
    first | exact superpose ef220 ef150860 | exact superpose ef150860 ef220
  have ef150878 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (x ◇ ((dr x y) ◇ (y ◇
      (dl (dr (dr y y) (((x ◇ y) ◇ y) ◇ x)) (dr (y ◇ x) y))))))) := by
    first | exact superpose ef1453 ef150869 | exact superpose ef150869 ef1453
  have ef150887 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (x ◇ ((dr x y) ◇ (y ◇
      ((y ◇ x) ◇ (y ◇ (dr (dr y y) (((x ◇ y) ◇ y) ◇ x))))))))) := by
    first | exact superpose ef85 ef150878 | exact superpose ef150878 ef85
  have ef150896 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (x ◇ ((dr x y) ◇ (y ◇
      ((y ◇ x) ◇ (y ◇ ((x ◇ (dr y y)) ◇ ((x ◇ y) ◇ y))))))))) := by
    first | exact superpose ef38 ef150887 | exact superpose ef150887 ef38
  have ef150905 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (x ◇ ((dr x y) ◇ (y ◇
      ((y ◇ x) ◇ (dl ((x ◇ y) ◇ y) (y ◇ x)))))))) := by
    first | exact superpose ef1479 ef150896 | exact superpose ef150896 ef1479
  have ef150914 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (x ◇ ((dr x y) ◇ (y ◇
      ((y ◇ x) ◇ (y ◇ (dr (x ◇ y) (y ◇ x))))))))) := by
    first | exact superpose ef324 ef150905 | exact superpose ef150905 ef324
  have ef150923 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ ((dr (y ◇ (x ◇
      ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))))) (y ◇
      (x ◇ (y ◇ (dl x x))))) ◇ (x ◇ ((dr x y) ◇ (y ◇
      ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y)))))))) := by
    first | exact superpose ef38 ef150914 | exact superpose ef150914 ef38
  have ef150930 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (((dr y x) ◇ (dr (y ◇
      (x ◇ (y ◇ (dl x x)))) ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇
      (y ◇ (dr y y))))) ◇ (x ◇ ((dr x y) ◇ (y ◇ ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y)))))))) := by
    first | exact superpose ef567 ef150923 | exact superpose ef150923 ef567
  have ef150933 :
      x ≠ (y ◇ (dr y y)) ◇ ((y ◇ y) ◇ (y ◇ ((dr (y ◇
      (x ◇ (y ◇ (dl x x)))) ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇
      (y ◇ (dr y y)))) ◇ ((dr x y) ◇ (y ◇ ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y)))))))) := by
    first | exact superpose ef392 ef150930 | exact superpose ef150930 ef392
  have ef150936 :
      x ≠ (y ◇ (dr y y)) ◇ (dl ((dr (y ◇ (x ◇
      (y ◇ (dl x x)))) ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇
      (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇
      (y ◇ (dr y y)))) ◇ ((dr x y) ◇ (y ◇ ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y)))))) y) := by
    first | exact superpose ef32 ef150933 | exact superpose ef150933 ef32
  have ef150939 :
      x ≠ (y ◇ (dr y y)) ◇ (((dr x y) ◇ (y ◇ ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y))))) ◇ (dr (dr (y ◇
      (x ◇ (y ◇ (dl x x)))) ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇
      (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇
      (y ◇ (dr y y)))) y)) := by
    first | exact superpose ef324 ef150936 | exact superpose ef150936 ef324
  have ef150941 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (dl (y ◇ ((y ◇ x) ◇
      (y ◇ ((x ◇ (x ◇ y)) ◇ y)))) (dr (dr (y ◇ (x ◇ (y ◇ (dl x x)))) ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y)))) y)))) := by
    first | exact superpose ef410 ef150939 | exact superpose ef150939 ef410
  have ef150943 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ ((dr (y ◇
      (x ◇ (y ◇ (dl x x)))) ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇
      (y ◇ (dr y y)))) ◇ (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y)))))))) := by
    first | exact superpose ef85 ef150941 | exact superpose ef150941 ef85
  have ef150944 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (((dr y x) ◇
      (dr ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))) (y ◇ (dl x x)))) ◇
      (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y)))))))) := by
    first | exact superpose ef567 ef150943 | exact superpose ef150943 ef567
  have ef150945 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇
      (dl (dr ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))) (y ◇ (dl x x))) (y ◇ (y ◇ ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y)))))))))) := by
    first | exact superpose ef410 ef150944 | exact superpose ef150944 ef410
  have ef150946 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((dr ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y))) y) ◇ (dr ((((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) ◇ (y ◇ (dr y y))) (y ◇ (dl x x))))))))) := by
    first | exact superpose ef220 ef150945 | exact superpose ef150945 ef220
  have ef150947 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((dr ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y))) y) ◇ ((dr (((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))) y) ◇ (dr (y ◇ (dl x x)) (dr y y))))))))) := by
    first | exact superpose ef567 ef150946 | exact superpose ef150946 ef567
  have ef150948 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((dr ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y))) y) ◇ (dl (dr (dl x x) (((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))))))) (dr y y)))))))) := by
    first | exact superpose ef1453 ef150947 | exact superpose ef150947 ef1453
  have ef150949 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((dr ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y))) y) ◇ (y ◇ (y ◇ (dr (dl x x) (((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x)))))) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))))))))))))))) := by
    first | exact superpose ef85 ef150948 | exact superpose ef150948 ef85
  have ef150950 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((dr ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y))) y) ◇ (y ◇ (y ◇ (((y ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))))) ◇ (dl x x)) ◇ ((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))))))))))))) := by
    first | exact superpose ef38 ef150949 | exact superpose ef150949 ef38
  have ef150951 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((dr ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y))) y) ◇ (y ◇ ((dl (dl x x) ((y ◇ y) ◇ (((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))))) ◇ ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))))))))) := by
    first | exact superpose ef10489 ef150950 | exact superpose ef150950 ef10489
  have ef150952 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((dr ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y))) y) ◇ (y ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (dr (dl x x) (dl ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))) (y ◇ y))))))))))) := by
    first | exact superpose ef2948 ef150951 | exact superpose ef150951 ef2948
  have ef150953 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((dr ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y))) y) ◇ (y ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ (dr (dl ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))) (y ◇ y)) x)))))))))) := by
    first | exact superpose ef527 ef150952 | exact superpose ef150952 ef527
  have ef150954 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((dr ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y))) y) ◇ (y ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (dr x ((y ◇ y) ◇ (x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))))))))))))))) := by
    first | exact superpose ef527 ef150953 | exact superpose ef150953 ef527
  have ef150955 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((dr ((y ◇ x) ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ y))) y) ◇ (y ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))) ◇ x) ◇ (y ◇ y)))))))))))) := by
    first | exact superpose ef38 ef150954 | exact superpose ef150954 ef38
  have ef150956 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      (((dr (y ◇ x) y) ◇ (dr y ((x ◇ (x ◇ y)) ◇ y))) ◇ (y ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))) ◇ x) ◇ (y ◇ y)))))))))))) := by
    first | exact superpose ef567 ef150955 | exact superpose ef150955 ef567
  have ef150957 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((dr y ((x ◇ (x ◇ y)) ◇ y)) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))) ◇ x) ◇ (y ◇ y)))))))))))) := by
    first | exact superpose ef392 ef150956 | exact superpose ef150956 ef392
  have ef150958 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((x ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))) ◇ x) ◇ (y ◇ y)))))))))))) := by
    first | exact superpose ef38 ef150957 | exact superpose ef150957 ef38
  have ef150994 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((dr ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) x) ◇ (dr (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))) x)) ◇ (y ◇ y)))))))))))) := by
    first | exact superpose ef1492 ef150958 | exact superpose ef150958 ef1492
  have ef151011 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (dl (dr (((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))) x) (y ◇ y)))))))))))))) := by
    first | exact superpose ef410 ef150994 | exact superpose ef150994 ef410
  have ef151027 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (dl ((dr ((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) x) ◇ (dr x (y ◇ ((x ◇ x) ◇ y)))) (y ◇ y)))))))))))))) := by
    first | exact superpose ef567 ef151011 | exact superpose ef151011 ef567
  have ef151038 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ ((dr x (y ◇ ((x ◇ x) ◇ y))) ◇ (dr (dr ((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) x) (y ◇ y))))))))))))))) := by
    first | exact superpose ef324 ef151027 | exact superpose ef151027 ef324
  have ef151049 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ ((dr x (y ◇ ((x ◇ x) ◇ y))) ◇ ((y ◇ (dr ((y ◇ y) ◇ ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x)))))) x)) ◇ y)))))))))))))) := by
    first | exact superpose ef38 ef151038 | exact superpose ef151038 ef38
  have ef151058 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ ((dr x (y ◇ ((x ◇ x) ◇ y))) ◇ ((y ◇ ((dr (y ◇ y) (y ◇ y)) ◇ (dr x (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x))))))) ◇ y)))))))))))))) := by
    first | exact superpose ef567 ef151049 | exact superpose ef151049 ef567
  have ef151065 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ ((dr x (y ◇ ((x ◇ x) ◇ y))) ◇ ((y ◇ ((dr (y ◇ y) (y ◇ y)) ◇ ((((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ ((y ◇ (x ◇ (dr x x))) ◇ y)))) ◇ y)))))))))))))) := by
    first | exact superpose ef38 ef151058 | exact superpose ef151058 ef38
  have ef151072 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ ((dr x (y ◇ ((x ◇ x) ◇ y))) ◇ ((y ◇ (((y ◇ (y ◇ y)) ◇ y) ◇ ((((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ ((y ◇ (x ◇ (dr x x))) ◇ y)))) ◇ y)))))))))))))) := by
    first | exact superpose ef38 ef151065 | exact superpose ef151065 ef38
  have ef151079 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ ((dr x (y ◇ ((x ◇ x) ◇ y))) ◇ (dr (y ◇ y) ((((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ ((y ◇ (x ◇ (dr x x))) ◇ y)))))))))))))))) := by
    first | exact superpose ef396 ef151072 | exact superpose ef151072 ef396
  have ef151084 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ ((dr x (y ◇ ((x ◇ x) ◇ y))) ◇ ((((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (y ◇ y)) ◇ (((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x))) ◇ x))))))))))))))) := by
    first | exact superpose ef38 ef151079 | exact superpose ef151079 ef38
  have ef151089 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ ((dr x (y ◇ ((x ◇ x) ◇ y))) ◇ ((dl y (y ◇ (x ◇ (dr x x)))) ◇ (((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x))) ◇ x))))))))))))))) := by
    first | exact superpose ef32 ef151084 | exact superpose ef151084 ef32
  have ef151090 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ ((dr x (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ (dr x x)) ◇ (dr y (dl (((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x))) ◇ x) y)))))))))))))))) := by
    first | exact superpose ef2948 ef151089 | exact superpose ef151089 ef2948
  have ef151091 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ ((dl (dr x x) (dr y (dl (((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x))) ◇ x) y))) ◇ (y ◇ ((x ◇ x) ◇ y))))))))))))))) := by
    first | exact superpose ef1605 ef151090 | exact superpose ef151090 ef1605
  have ef151092 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (x ◇ (x ◇ ((dr (y ◇ ((x ◇ x) ◇ y)) (dr y (dl (((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x))) ◇ x) y))) ◇ x)))))))))))))) := by
    first | exact superpose ef1285 ef151091 | exact superpose ef151091 ef1285
  have ef151093 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (dr x (dr (y ◇ ((x ◇ x) ◇ y)) (dr y (dl (((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x))) ◇ x) y))))))))))))))) := by
    first | exact superpose ef25 ef151092 | exact superpose ef151092 ef25
  have ef151094 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ ((dr y (dl (((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x))) ◇ x) y)) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))))))))) := by
    first | exact superpose ef63 ef151093 | exact superpose ef151093 ef63
  have ef151095 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ ((((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x))) ◇ x) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))))))))))) := by
    first | exact superpose ef19 ef151094 | exact superpose ef151094 ef19
  have ef151096 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ (dl (y ◇ ((x ◇ x) ◇ y)) ((y ◇ y) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ x) ◇ x))))))))))))))) := by
    first | exact superpose ef32 ef151095 | exact superpose ef151095 ef32
  have ef151097 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((dr ((x ◇ x) ◇ x) (y ◇ y)) ◇ (y ◇ ((x ◇ x) ◇ y))))))))))))))) := by
    first | exact superpose ef220 ef151096 | exact superpose ef151096 ef220
  have ef151098 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ (((dl (y ◇ y) (x ◇ x)) ◇ x) ◇ (y ◇ ((x ◇ x) ◇ y))))))))))))))) := by
    first | exact superpose ef514 ef151097 | exact superpose ef151097 ef514
  have ef151099 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ ((x ◇ (dr (y ◇ y) (dl x x))) ◇ (y ◇ ((x ◇ x) ◇ y))))))))))))))) := by
    first | exact superpose ef2948 ef151098 | exact superpose ef151098 ef2948
  have ef151118 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ (y ◇ (y ◇ ((x ◇ x) ◇ (x ◇ (dr (y ◇ y) (dl x x)))))))))))))))))) := by
    first | exact superpose ef18347 ef151099 | exact superpose ef151099 ef18347
  have ef151135 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ (y ◇ (y ◇ (dl (dr (y ◇ y) (dl x x)) x))))))))))))))) := by
    first | exact superpose ef32 ef151118 | exact superpose ef151118 ef32
  have ef151140 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ (y ◇ (y ◇ (dl x (y ◇ y)))))))))))))))) := by
    first | exact superpose ef8486 ef151135 | exact superpose ef151135 ef8486
  have ef151145 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ (((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) ◇ ((x ◇ (y ◇ ((x ◇ x) ◇ y))) ◇ (y ◇ (x ◇ y)))))))))))))) := by
    first | exact superpose ef2795 ef151140 | exact superpose ef151140 ef2795
  have ef151184 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((dl (y ◇ ((x ◇ x) ◇ y)) (y ◇ (x ◇ y))) ◇ (dl ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) x)))))))))))) := by
    first | exact superpose ef2886 ef151145 | exact superpose ef151145 ef2886
  have ef151193 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (dr (y ◇ ((x ◇ x) ◇ y)) (dl (dl ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) x) y))))))))))))) := by
    first | exact superpose ef2948 ef151184 | exact superpose ef151184 ef2948
  have ef151198 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ ((dr y (x ◇ x)) ◇ (dr (dl (dl ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) x) y) y))))))))))))) := by
    first | exact superpose ef567 ef151193 | exact superpose ef151193 ef567
  have ef151203 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ ((dr y (x ◇ x)) ◇ (y ◇ (dr y (dl ((y ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x))) x))))))))))))))) := by
    first | exact superpose ef527 ef151198 | exact superpose ef151198 ef527
  have ef151208 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ ((dr y (x ◇ x)) ◇ (y ◇ (dr y ((((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x)) ◇ (dr (y ◇ y) x)))))))))))))))) := by
    first | exact superpose ef324 ef151203 | exact superpose ef151203 ef324
  have ef151212 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ ((dr y (x ◇ x)) ◇ (y ◇ (((dr (y ◇ y) x) ◇ y) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x)))))))))))))))) := by
    first | exact superpose ef38 ef151208 | exact superpose ef151208 ef38
  have ef151216 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ ((dr y (x ◇ x)) ◇ (y ◇ ((y ◇ y) ◇ (x ◇ (dl y (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x)))))))))))))))))) := by
    first | exact superpose ef410 ef151212 | exact superpose ef151212 ef410
  have ef151219 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ ((dr y (x ◇ x)) ◇ (y ◇ ((y ◇ x) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x)))))))))))))))) := by
    first | exact superpose ef11293 ef151216 | exact superpose ef151216 ef11293
  have ef151222 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ ((y ◇ x) ◇ (((y ◇ (x ◇ (dr x x))) ◇ y) ◇ (x ◇ x)))))))))))))))) := by
    first | exact superpose ef38 ef151219 | exact superpose ef151219 ef38
  have ef151231 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ ((y ◇ x) ◇ (((dr x y) ◇ (dr (dr x x) y)) ◇ (x ◇ x)))))))))))))))) := by
    first | exact superpose ef1492 ef151222 | exact superpose ef151222 ef1492
  have ef151244 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ ((y ◇ x) ◇ (x ◇ (y ◇ (dl (dr (dr x x) y) (x ◇ x)))))))))))))))))) := by
    first | exact superpose ef410 ef151231 | exact superpose ef151231 ef410
  have ef151247 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (dl (y ◇ (dl (dr (dr x x) y) (x ◇ x))) y)))))))))))))) := by
    first | exact superpose ef32 ef151244 | exact superpose ef151244 ef32
  have ef151250 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ ((dl (dr (dr x x) y) (x ◇ x)) ◇ (dr y y))))))))))))))) := by
    first | exact superpose ef324 ef151247 | exact superpose ef151247 ef324
  have ef151253 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ (dr (dr (dr x x) y) (dl (dr y y) x)))))))))))))))) := by
    first | exact superpose ef2948 ef151250 | exact superpose ef151250 ef2948
  have ef151256 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dl (dl (dr y y) x) y) ◇ (dr x x)))))))))))))))) := by
    first | exact superpose ef517 ef151253 | exact superpose ef151253 ef517
  have ef151259 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ (((y ◇ (dr y y)) ◇ x) ◇ (dr x x)))))))))))))))) := by
    first | exact superpose ef137 ef151256 | exact superpose ef151256 ef137
  have ef151278 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ ((((x ◇ x) ◇ x) ◇ x) ◇ ((y ◇ (x ◇ (x ◇ (dl y x)))) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ (((y ◇ (dr y y)) ◇ x) ◇ (dr x x)))))))))))))))) := by
    first | exact superpose ef2374 ef151259 | exact superpose ef151259 ef2374
  have ef151584 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (((dr x x) ◇ (x ◇ x)) ◇ ((y ◇ (x ◇ (x ◇ (dl y x)))) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ (((y ◇ (dr y y)) ◇ x) ◇ (dr x x)))))))))))))))) := by
    first | exact superpose ef12879 ef151278 | exact superpose ef151278 ef12879
  have ef151601 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ (dl (x ◇ x) ((y ◇ (x ◇ (x ◇ (dl y x)))) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ (((y ◇ (dr y y)) ◇ x) ◇ (dr x x)))))))))))))))))) := by
    first | exact superpose ef410 ef151584 | exact superpose ef151584 ef410
  have ef151604 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((dr ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ (((y ◇ (dr y y)) ◇ x) ◇ (dr x x)))))) (y ◇ (x ◇ (x ◇ (dl y x))))) ◇ (x ◇ x)))))))))))) := by
    first | exact superpose ef220 ef151601 | exact superpose ef151601 ef220
  have ef151605 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ (((dr (x ◇ y) ((x ◇ y) ◇ x)) ◇ (dr (y ◇ (x ◇ (x ◇ (dl y x)))) (y ◇ (x ◇ (((y ◇ (dr y y)) ◇ x) ◇ (dr x x)))))) ◇ (x ◇ x)))))))))))) := by
    first | exact superpose ef567 ef151604 | exact superpose ef151604 ef567
  have ef151606 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (dl (dr (y ◇ (x ◇ (x ◇ (dl y x)))) (y ◇ (x ◇ (((y ◇ (dr y y)) ◇ x) ◇ (dr x x))))) (x ◇ x)))))))))))))) := by
    first | exact superpose ef410 ef151605 | exact superpose ef151605 ef410
  have ef151607 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (dl ((dr y x) ◇ (dr (y ◇ (x ◇ (((y ◇ (dr y y)) ◇ x) ◇ (dr x x)))) (x ◇ (dl y x)))) (x ◇ x)))))))))))))) := by
    first | exact superpose ef567 ef151606 | exact superpose ef151606 ef567
  have ef151608 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ ((dr (y ◇ (x ◇ (((y ◇ (dr y y)) ◇ x) ◇ (dr x x)))) (x ◇ (dl y x))) ◇ (dr (dr y x) (x ◇ x))))))))))))))) := by
    first | exact superpose ef324 ef151607 | exact superpose ef151607 ef324
  have ef151609 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ ((dr (y ◇ (x ◇ (((y ◇ (dr y y)) ◇ x) ◇ (dr x x)))) (x ◇ (dl y x))) ◇ ((x ◇ (dr y x)) ◇ x)))))))))))))) := by
    first | exact superpose ef38 ef151608 | exact superpose ef151608 ef38
  have ef151610 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (((dr y x) ◇ (dr (x ◇ (dl y x)) (((y ◇ (dr y y)) ◇ x) ◇ (dr x x)))) ◇ ((x ◇ (dr y x)) ◇ x)))))))))))))) := by
    first | exact superpose ef567 ef151609 | exact superpose ef151609 ef567
  have ef151611 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ (dl (dr (x ◇ (dl y x)) (((y ◇ (dr y y)) ◇ x) ◇ (dr x x))) ((x ◇ (dr y x)) ◇ x)))))))))))))))) := by
    first | exact superpose ef410 ef151610 | exact superpose ef151610 ef410
  have ef151612 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ ((x ◇ x) ◇ (dr (x ◇ (dl y x)) (((y ◇ (dr y y)) ◇ x) ◇ (dr x x))))))))))))))))))) := by
    first | exact superpose ef146 ef151611 | exact superpose ef151611 ef146
  have ef151613 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ ((x ◇ x) ◇ (((dr x x) ◇ (x ◇ (dl y x))) ◇ ((y ◇ (dr y y)) ◇ x)))))))))))))))))) := by
    first | exact superpose ef38 ef151612 | exact superpose ef151612 ef38
  have ef151614 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ ((x ◇ x) ◇ (x ◇ (x ◇ (dl (x ◇ (dl y x)) ((y ◇ (dr y y)) ◇ x)))))))))))))))))))) := by
    first | exact superpose ef410 ef151613 | exact superpose ef151613 ef410
  have ef151615 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ (dl (x ◇ (dl (x ◇ (dl y x)) ((y ◇ (dr y y)) ◇ x))) x)))))))))))))))) := by
    first | exact superpose ef32 ef151614 | exact superpose ef151614 ef32
  have ef151616 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ ((dl (x ◇ (dl y x)) ((y ◇ (dr y y)) ◇ x)) ◇ (dr x x))))))))))))))))) := by
    first | exact superpose ef324 ef151615 | exact superpose ef151615 ef324
  have ef151617 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (dr (x ◇ (dl y x)) (dl (dr x x) (y ◇ (dr y y)))))))))))))))))))) := by
    first | exact superpose ef2948 ef151616 | exact superpose ef151616 ef2948
  have ef151618 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (dr (x ◇ (dl y x)) ((dl y y) ◇ (y ◇ (dr x x)))))))))))))))))))) := by
    first | exact superpose ef701 ef151617 | exact superpose ef151617 ef701
  have ef151619 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (((y ◇ (dr x x)) ◇ (x ◇ (dl y x))) ◇ (dl y y)))))))))))))))))) := by
    first | exact superpose ef38 ef151618 | exact superpose ef151618 ef38
  have ef151762 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (y ◇ ((x ◇ (dl y x)) ◇ (dr (y ◇ (dr x x)) y))))))))))))))))))) := by
    first | exact superpose ef1298 ef151619 | exact superpose ef151619 ef1298
  have ef151781 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (y ◇ (x ◇ (dr ((dr (y ◇ (dr x x)) y) ◇ y) x))))))))))))))))))) := by
    first | exact superpose ef10722 ef151762 | exact superpose ef151762 ef10722
  have ef151790 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (y ◇ (x ◇ (dr (y ◇ (dr x x)) x))))))))))))))))))) := by
    first | exact superpose ef14 ef151781 | exact superpose ef151781 ef14
  have ef151799 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ (((y ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))))))))))))))) := by
    first | exact superpose ef10491 ef151790 | exact superpose ef151790 ef10491
  have ef151817 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ (x ◇ (x ◇ (y ◇ y)))) ◇ (x ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))))))))))))))) := by
    first | exact superpose ef18347 ef151799 | exact superpose ef151799 ef18347
  have ef151975 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ (x ◇ (y ◇ y))) ◇ (x ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))))))))))))))) := by
    first | exact superpose ef2374 ef151817 | exact superpose ef151817 ef2374
  have ef152599 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ (y ◇ y)) ◇ ((y ◇ y) ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))))))))))))))) := by
    first | exact superpose ef2827 ef151975 | exact superpose ef151975 ef2827
  have ef152602 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (dl ((x ◇ y) ◇ (((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y)))))))) x))))))))) := by
    first | exact superpose ef32 ef152599 | exact superpose ef152599 ef32
  have ef152606 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ ((((x ◇ y) ◇ x) ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))) ◇ (dr (x ◇ y) x)))))))))) := by
    first | exact superpose ef324 ef152602 | exact superpose ef152602 ef324
  have ef152615 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))) ◇ (dr (x ◇ y) ((x ◇ y) ◇ x))))))))))) := by
    first | exact superpose ef10490 ef152606 | exact superpose ef152606 ef10490
  have ef152622 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ ((x ◇ (y ◇ (x ◇ ((dr y x) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))))) ◇ ((x ◇ (x ◇ y)) ◇ (x ◇ y))))))))))) := by
    first | exact superpose ef38 ef152615 | exact superpose ef152615 ef38
  have ef157109 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ ((dr y ((x ◇ (x ◇ y)) ◇ (x ◇ y))) ◇ (dr (x ◇ ((dr y x) ◇ (x ◇ (y ◇ ((x ◇ x) ◇ y))))) x)))))))))) := by
    first | exact superpose ef1492 ef152622 | exact superpose ef152622 ef1492
  have ef157122 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ ((dr y ((x ◇ (x ◇ y)) ◇ (x ◇ y))) ◇ ((dr x (dr y x)) ◇ (dr x (x ◇ (y ◇ ((x ◇ x) ◇ y)))))))))))))) := by
    first | exact superpose ef567 ef157109 | exact superpose ef157109 ef567
  have ef157124 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ ((dr y ((x ◇ (x ◇ y)) ◇ (x ◇ y))) ◇ ((dr x (dr y x)) ◇ (((y ◇ ((x ◇ x) ◇ y)) ◇ x) ◇ x))))))))))) := by
    first | exact superpose ef38 ef157122 | exact superpose ef157122 ef38
  have ef157126 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ ((dr y ((x ◇ (x ◇ y)) ◇ (x ◇ y))) ◇ ((dr x (dr y x)) ◇ ((x ◇ (dr y y)) ◇ x))))))))))) := by
    first | exact superpose ef2032 ef157124 | exact superpose ef157124 ef2032
  have ef157127 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ ((dr y ((x ◇ (x ◇ y)) ◇ (x ◇ y))) ◇ ((dl (dr y y) x) ◇ (dr y x))))))))))) := by
    first | exact superpose ef1605 ef157126 | exact superpose ef157126 ef1605
  have ef157128 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ ((dr y ((x ◇ (x ◇ y)) ◇ (x ◇ y))) ◇ (y ◇ ((dr (dr y x) x) ◇ y))))))))))) := by
    first | exact superpose ef1285 ef157127 | exact superpose ef157127 ef1285
  have ef157129 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ ((dr y ((x ◇ (x ◇ y)) ◇ (x ◇ y))) ◇ (y ◇ (((dl x x) ◇ y) ◇ y))))))))))) := by
    first | exact superpose ef517 ef157128 | exact superpose ef157128 ef517
  have ef157130 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ ((((x ◇ y) ◇ y) ◇ (x ◇ (x ◇ y))) ◇ (y ◇ (((dl x x) ◇ y) ◇ y))))))))))) := by
    first | exact superpose ef38 ef157129 | exact superpose ef157129 ef38
  have ef157131 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ ((y ◇ (x ◇ (x ◇ ((x ◇ y) ◇ y)))) ◇ (y ◇ (((dl x x) ◇ y) ◇ y))))))))))) := by
    first | exact superpose ef18347 ef157130 | exact superpose ef157130 ef18347
  have ef157150 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ (((dl x x) ◇ y) ◇ (y ◇ (x ◇ (x ◇ ((x ◇ y) ◇ y))))))))))))))) := by
    first | exact superpose ef18347 ef157131 | exact superpose ef157131 ef18347
  have ef157155 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ (dl (x ◇ (x ◇ ((x ◇ y) ◇ y))) (dl x x)))))))))))) := by
    first | exact superpose ef32 ef157150 | exact superpose ef157150 ef32
  have ef157157 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ ((dl x (x ◇ (x ◇ ((x ◇ y) ◇ y)))) ◇ x))))))))))) := by
    first | exact superpose ef946 ef157155 | exact superpose ef157155 ef946
  have ef157159 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (x ◇ (y ◇
      ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ ((x ◇ ((x ◇ y) ◇ y)) ◇ (dr x (dl x x))))))))))))) := by
    first | exact superpose ef2948 ef157157 | exact superpose ef157157 ef2948
  have ef157161 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇
      (x ◇ (y ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ x) ◇ (y ◇ (y ◇ ((x ◇ ((x ◇ y) ◇ y)) ◇ x))))))))))) := by
    first | exact superpose ef19 ef157159 | exact superpose ef157159 ef19
  have ef157167 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇
      (x ◇ (y ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (x ◇ (y ◇ ((x ◇ ((x ◇ y) ◇ y)) ◇ x))))))))))) := by
    first | exact superpose ef2827 ef157161 | exact superpose ef157161 ef2827
  have ef157170 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇
      (y ◇ (y ◇ (x ◇ (y ◇ ((y ◇ x) ◇ ((y ◇ x) ◇ ((x ◇ y) ◇ (dr y (x ◇ ((x ◇ y) ◇ y))))))))))) := by
    first | exact superpose ef25 ef157167 | exact superpose ef157167 ef25
  have ef157174 :
      x ≠ (y ◇ (dr y y)) ◇
      (x ◇ (y ◇ (y ◇ (x ◇ (y ◇ ((y ◇ x) ◇ (dr (x ◇ y) (dl (x ◇ ((x ◇ y) ◇ y)) x)))))))) := by
    first | exact superpose ef538 ef157170 | exact superpose ef157170 ef538
  have ef157178 :
      x ≠ (y ◇ (dr y y)) ◇
      (x ◇ (y ◇ (y ◇ (x ◇ (y ◇ (((dl (x ◇ ((x ◇ y) ◇ y)) x) ◇ x) ◇ x)))))) := by
    first | exact superpose ef1502 ef157174 | exact superpose ef157174 ef1502
  have ef157182 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (dr y ((dl (x ◇ ((x ◇ y) ◇ y)) x) ◇ x))))) := by
    first | exact superpose ef25 ef157178 | exact superpose ef157178 ef25
  have ef157186 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ ((x ◇ y) ◇ (dl (x ◇ ((x ◇ y) ◇ y)) x))))) := by
    first | exact superpose ef38 ef157182 | exact superpose ef157182 ef38
  have ef157190 :
      x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ ((x ◇ y) ◇ (((x ◇ y) ◇ y) ◇ (dr x x)))))) := by
    first | exact superpose ef324 ef157186 | exact superpose ef157186 ef324
  have ef157194 : x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ (dr ((x ◇ y) ◇ y) (dl x y))))) := by
    first | exact superpose ef538 ef157190 | exact superpose ef157190 ef538
  have ef157198 : x ≠ (y ◇ (dr y y)) ◇ (x ◇ (y ◇ (y ◇ ((dl (dl x y) (y ◇ x)) ◇ y)))) := by
    first | exact superpose ef514 ef157194 | exact superpose ef157194 ef514
  have ef157202 : x ≠ (y ◇ (dr y y)) ◇ (x ◇ (dr y (dl (dl x y) (y ◇ x)))) := by
    first | exact superpose ef25 ef157198 | exact superpose ef157198 ef25
  have ef157206 : x ≠ dr x (dl (dl (dl x y) (y ◇ x)) (dr y y)) := by
    first | exact superpose ef538 ef157202 | exact superpose ef157202 ef538
  have ef157210 : x ≠ dr x (y ◇ (y ◇ (dl (dl x y) (y ◇ x)))) := by
    first | exact superpose ef85 ef157206 | exact superpose ef157206 ef85
  have ef157214 : x ≠ ((y ◇ (dl (dl x y) (y ◇ x))) ◇ x) ◇ y := by
    first | exact superpose ef38 ef157210 | exact superpose ef157210 ef38
  have ef157218 : x ≠ ((y ◇ x) ◇ (dr (x ◇ (dl x y)) y)) ◇ y := by
    first | exact superpose ef10722 ef157214 | exact superpose ef157214 ef10722
  have ef157222 : x ≠ (dr x (x ◇ (dl x y))) ◇ y := by
    first | exact superpose ef71 ef157218 | exact superpose ef157218 ef71
  have ef157226 : x ≠ (((dl x y) ◇ x) ◇ x) ◇ y := by
    first | exact superpose ef38 ef157222 | exact superpose ef157222 ef38
  subsumption ef157226 ef54

theorem Equation504_termDefinableFromFin_Equation898 :
    Law504.TermDefinableFromFin Law898 := by
  refine termDefinableFromFin_of_qterm (.rdv (.ldv (.rdv (.var 0) (.var 0)) (.op (.op (.var 0) (.var 0)) (.op (.var 1) (.var 1)))) (.op (.var 0) (.var 1))) ?_ ?_ ?_
  · intro G _ M hGL b
    exact @inj898R G _ M (Law898.models_iff.mp hGL) b
  · intro G _ M hGL a
    exact @inj898L G _ M (Law898.models_iff.mp hGL) a
  · intro G _ M hGL dr dl h1 h2 h3 h4
    rw [@Law504.models_iff]
    exact fun x y ↦
      @aux898_504 G _ M (Law898.models_iff.mp hGL) dr dl h1 h2 h3 h4 x y

end Law.MagmaLaw
