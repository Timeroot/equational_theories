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
    (wf : G → G → G) (hwdef : ∀ a b : G, wf a b = b ◇ (b ◇ a)) (x y : G) :
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

end Law.MagmaLaw
