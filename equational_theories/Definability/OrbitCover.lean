import equational_theories.Definability.OrbitWitness
import equational_theories.Equations.All
import equational_theories.Superposition

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
-- which of the two inverse equations a proof reaches is Vampire's business, not ours
set_option linter.unusedVariables false

/-!
# Term-definability facts whose witness is named by an equation

The cells here are the ones no single term settles. `Definability/PositiveTermsFin.lean` looks for
one binary term that defines the target in every finite model of the source at once, and
`Definability/QuasigroupCover.lean` widens the search to terms in `◇`, `/` and `\`; both are still
searches for a *term*, and the sweeps behind them are exhaustive at the sizes a prover can handle.

`Definability/OrbitWitness.lean` names the witness differently. Fix a hole term `g(x, y, -)`, a
base term `t(x, y)` and an offset `j`. If filling the hole is injective then on a finite carrier it
is a permutation, so the orbit of `t` under it is a cycle and

    g^{j+1}(w) = t

has a solution `w` inside that orbit -- and every point of the orbit is a term, of a depth the
magma chooses. That is exactly the freedom `TermDefinableFromFin` grants and `TermDefinableFrom`
does not, and the defining property of `w` is an equation that never mentions the magma.

Division is the corner of this space where `g` is a translation: `w ◇ x = y` says `w = y / x`.
Everything else is new, and it does not ask the source to force a quasigroup -- only that one hole
term be injective.

Each cell contributes two replayed lemmas: `inj<s>_<g>`, that the source forces the hole map
injective, and `aux<s>_<t>_<g>`, that the target holds of any `wf` the orbit equation names. The
second is stated in a structure carrying a two-sided inverse `gi` of the hole map, which
`exists_hinv` extracts from injectivity and finiteness; superposition rewrites with `gi`, whereas
the orbit equation alone buries `wf` under `j+1` copies of `g` with nothing to peel them off.
-/

open FirstOrder FirstOrder.Language
open Law
open Law.MagmaLaw

namespace Law.MagmaLaw

variable {G : Type}

/-- On a finite carrier a one-sided inverse is two-sided: this is what turns a source law into its
cyclic rotations. -/
private theorem rot_of_finite [Finite G] {f g : G → G} (hfg : ∀ z, f (g z) = z) (x : G) :
    g (f x) = x := by
  have hs : Function.Surjective f := fun z ↦ ⟨g z, hfg z⟩
  exact Finite.injective_iff_surjective.mpr hs (hfg (f x))

section Source467

/-- Filling the hole of `(x◇(-◇-))` is injective in every finite magma satisfying equation 467
`x = y ◇ (x ◇ (x ◇ (y ◇ y)))`, so on a finite carrier it is a permutation and the orbit of any
term closes up. -/
private theorem inj467_44544 [Finite G] [Magma G] (h : Equation467 G) (x y : G) :
    Function.Injective (fun a : G ↦ x ◇ (a ◇ a)) := by
  intro p q hhyp
  replace hhyp : x ◇ (p ◇ p) = x ◇ (q ◇ q) := hhyp
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef8 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef9 : x ◇ (p ◇ p) = x ◇ (q ◇ q) := mod_symm hhyp
  have ef10 : p ≠ q := mod_symm nh
  have ef13 : q ◇ q = (x ◇ (p ◇ p)) ◇ ((x ◇ (p ◇ p)) ◇ (x ◇ x)) := by
    first | exact superpose ef9 ef8 | exact superpose ef8 ef9
  have ef16 : p ◇ p = q ◇ q := by
    first | exact superpose ef8 ef13 | exact superpose ef13 ef8
  have ef19 : q = (p ◇ p) ◇ ((p ◇ p) ◇ (p ◇ p)) := by
    first | exact superpose ef16 ef8 | exact superpose ef8 ef16
  have ef20 : p = q := by
    first | exact superpose ef8 ef19 | exact superpose ef19 ef8
  subsumption ef20 ef10

/-- Equation 504 `x = y ◇ (y ◇ (x ◇ (y ◇ y)))` holds of any operation `wf` with
`a ◇ (wf a b ◇ wf a b) = b ◇ b`, in every finite magma satisfying equation 467
`x = y ◇ (x ◇ (x ◇ (y ◇ y)))`. The orbit argument of `OrbitWitness.lean` says such a `wf` is a
term. -/
private theorem aux467_504_05039 [Finite G] [Magma G] (h : Equation467 G)
    (gi : G → G → G → G) (hgs : ∀ a b c : G, a ◇ (gi a b c ◇ gi a b c) = c)
    (hgv : ∀ a b c : G, gi a b (a ◇ (c ◇ c)) = c)
    (wf : G → G → G)
    (hwdef : ∀ a b : G, a ◇ (wf a b ◇ wf a b) = b ◇ b)
    (x y : G) :
    x = wf y (wf y (wf x (wf y y))) := by
  by_contra nh
  have hrot0 (a b : G) : (b ◇ a) ◇ ((b ◇ a) ◇ (b ◇ b)) = a :=
    rot_of_finite (f := fun z ↦ b ◇ z) (g := fun z ↦ z ◇ (z ◇ (b ◇ b)))
      (fun z ↦ (h z b).symm) a
  have ef10 (X0 X1 : G) : (X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (hrot0 ..)
  have ef11 (X0 X1 X2 : G) : X0 ◇ ((gi X0 X1 X2) ◇ (gi X0 X1 X2)) = X2 := mod_symm (hgs ..)
  have ef12 (X0 X1 X2 : G) : gi X0 X1 (X0 ◇ (X2 ◇ X2)) = X2 := mod_symm (hgv ..)
  have ef13 (X0 X1 : G) : X1 ◇ X1 = X0 ◇ ((wf X0 X1) ◇ (wf X0 X1)) := mod_symm (hwdef ..)
  have ef14 : x ≠ wf y (wf y (wf x (wf y y))) := mod_symm nh
  have ef21 (X0 X1 X2 : G) : X0 ◇ (X0 ◇ (X1 ◇ X1)) = (gi X1 X2 X0) ◇ (gi X1 X2 X0) := by
    first | exact superpose ef11 ef10 | exact superpose ef10 ef11
  have ef56 (X0 X1 X2 : G) : wf X1 X0 = gi X1 X2 (X0 ◇ X0) := by
    first | exact superpose ef13 ef12 | exact superpose ef12 ef13
  have ef58 (X0 X1 : G) : (wf X1 X0) ◇ (wf X1 X0) = (X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    first | exact superpose ef13 ef10 | exact superpose ef10 ef13
  have ef142 (X0 X1 X2 X3 X4 : G) : gi X1 X4 X0 = gi X2 X3 (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    first | exact superpose ef21 ef12 | exact superpose ef12 ef21
  have ef146 (X0 X1 X2 X3 X4 : G) : wf X2 (gi X1 X3 X0) = gi X2 X4 (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    first | exact superpose ef21 ef56 | exact superpose ef56 ef21
  have ef299 (X0 : G) : (wf X0 X0) ◇ (wf X0 X0) = X0 := by
    first | exact superpose ef10 ef58 | exact superpose ef58 ef10
  have ef323 (X0 X1 X2 : G) : wf X0 X0 = gi X1 X2 (X1 ◇ X0) := by
    first | exact superpose ef299 ef12 | exact superpose ef12 ef299
  have ef329 (X0 X1 X2 : G) : gi X1 X2 X0 = wf X1 (wf X0 X0) := by
    first | exact superpose ef299 ef56 | exact superpose ef56 ef299
  have ef544 (X0 : G) : x ≠ wf y (wf y (gi x X0 y)) := by
    first | exact superpose ef329 ef14 | exact superpose ef14 ef329
  have ef2188 (X0 X1 : G) : x ≠ wf y (wf y (gi X0 X1 (X0 ◇ (y ◇ (y ◇ (x ◇ x)))))) := by
    first | exact superpose ef142 ef544 | exact superpose ef544 ef142
  have ef2378 : x ≠ wf y (wf y (wf (y ◇ (y ◇ (x ◇ x))) (y ◇ (y ◇ (x ◇ x))))) := by
    first | exact superpose ef323 ef2188 | exact superpose ef2188 ef323
  have ef2421 (X0 : G) : x ≠ wf y (gi y X0 (y ◇ (y ◇ (x ◇ x)))) := by
    first | exact superpose ef329 ef2378 | exact superpose ef2378 ef329
  have ef2599 (X0 : G) : x ≠ gi y X0 ((y ◇ (y ◇ (x ◇ x))) ◇ ((y ◇ (y ◇ (x ◇ x))) ◇ (y ◇ y))) := by
    first | exact superpose ef146 ef2421 | exact superpose ef2421 ef146
  have ef2648 (X0 : G) : x ≠ gi y X0 (y ◇ (x ◇ x)) := by
    first | exact superpose ef10 ef2599 | exact superpose ef2599 ef10
  subsumption ef2648 ef12

theorem Equation504_termDefinableFromFin_Equation467 :
    Law504.TermDefinableFromFin Law467 := by
  refine termDefinableFromFin_of_orbit 0 (fun G ↦ (hmul (Term.var 0) (hmul (Term.var 2) (Term.var 2)))) (fun G ↦ (bmul (Term.var 1) (Term.var 1))) ?_ ?_
  · intro G _ M hGL x y
    exact @inj467_44544 G _ M (Law467.models_iff.mp hGL) x y
  · intro G _ M hGL w hw
    obtain ⟨gi, hgs, hgv⟩ := exists_hinv M (hmul (Term.var 0) (hmul (Term.var 2) (Term.var 2)))
      (fun x y ↦ @inj467_44544 G _ M (Law467.models_iff.mp hGL) x y)
    rw [@Law504.models_iff]
    exact fun x y ↦
      @aux467_504_05039 G _ M (Law467.models_iff.mp hGL) gi hgs hgv w (fun a b ↦ hw a b) x y

end Source467

end Law.MagmaLaw
