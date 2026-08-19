import equational_theories.Definability.Clone
import equational_theories.Definability.FiniteFlavour
import Mathlib.Data.ZMod.Basic

/-!
# Clones that are too big to list: the translation-invariant families

Every clone certificate up to now has been a *list*: `C : Fin k → Magma G`, together with a `k × k`
composition table. That caps `k` at a few hundred and made `Definability/CloneExtra5.lean` and
`Definability/CloneExtra6.lean` enormous generated files. This file gets an unlistable clone for
free, by describing the family with a formula instead.

Let `G` be a group, written additively, and let `h : G → G`. Put

    x ◇ y = x + h (-x + y).

These are exactly the operations invariant under left translation, `(g + x) ◇ (g + y) = g + (x ◇ y)`
— the "regular" operations, the name this file takes. Three facts make them a clone family for any
one of themselves:

* left translation is an automorphism of each of them, which is `Magma.transOp_add_left`;
* consequently composition is *pointwise in `h`*: composing `x + h₁ (-x + y)` and `x + h₂ (-x + y)`
  along `x + h₀ (-x + y)` gives `x + h (-x + y)` with `h z = h₁ z + h₀ (-(h₁ z) + h₂ z)`, i.e. with
  `h` the composite of `h₁` and `h₂` computed in the magma itself;
* the two projections are `h = 0` and `h = id`, since `x + 0 = x` and `x + (-x + y) = y`.

So `Magma.transOp` is a clone family indexed by the function type `G → G`, with no enumeration and
no table whatsoever, and it contains the clone of `Magma.transOp h₀` for every `h₀`. For that to be
possible `Magma.IsCloneFamily` had to stop insisting on a `Fin k` index; nothing in its proofs ever
used finiteness, so `Definability/Clone.lean` now takes an arbitrary index type.

The payoff is the certificate condition. Refuting a target `L` no longer means checking `k` listed
operations, it means checking `∀ h : G → G, ¬ satisfies (transOp h) L` — a single quantifier over a
function type, which on a finite `G` is `Decidable` outright. On `ZMod 5` that is 3125 operations,
more than ten times the largest listed clone in this development, at a fraction of the source size.

The models are finite, so these refute `TermDefinableFromFin`, the finite flavour, which is the
stronger of the two directions: `Law.MagmaLaw.not_termDefinableFromFin_of_clone` is the finite-magma
counterpart of `Law.MagmaLaw.not_termDefinableFrom_of_clone`, and
`Law.MagmaLaw.not_termDefinableFromFin_of_transClone` packages it together with the clone family so
that a certificate is nothing but an `h₀` and a list of targets. See
`Definability/RegularCover.lean` for what one looks like.

As with every clone argument this says nothing about first-order definability.
-/

open Law Law.MagmaLaw

namespace Magma

variable {G : Type} [AddGroup G]

/-- The regular magma `x ◇ y = x + h (-x + y)` attached to `h : G → G`. These are exactly the
operations on `G` invariant under left translation. -/
@[implicit_reducible]
def transOp (h : G → G) : Magma G := ⟨fun x y ↦ x + h (-x + y)⟩

@[simp]
theorem transOp_op (h : G → G) (x y : G) : (transOp h).op x y = x + h (-x + y) := rfl

/-- Left translation is an automorphism of every regular operation. This is the whole content of
the file: it is what makes composition pointwise in `h`. -/
theorem transOp_add_left (h : G → G) (g x y : G) :
    (transOp h).op (g + x) (g + y) = g + (transOp h).op x y := by
  have hgxy : -(g + x) + (g + y) = -x + y := by
    rw [neg_add_rev, add_assoc, neg_add_cancel_left]
  simp only [transOp_op, hgxy, add_assoc]

/-- Where the composite of two regular operations lands: pointwise in the index, computed in the
magma `Magma.transOp h₀` itself. -/
def transComp (h₀ h₁ h₂ : G → G) : G → G := fun z ↦ (transOp h₀).op (h₁ z) (h₂ z)

/-- **The regular clone family.** The regular operations on `G`, indexed by `G → G`, contain both
projections and are closed under composition along any one of them. No enumeration and no
composition table: the index is a function type and the composition map is a formula. -/
theorem transOp_isCloneFamily (h₀ : G → G) :
    (transOp h₀).IsCloneFamily transOp 0 id (transComp h₀) where
  fst x y := by simp
  snd x y := by simp
  comp h₁ h₂ x y := (transOp_add_left h₀ x (h₁ (-x + y)) (h₂ (-x + y))).symm

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- **Clone obstruction, finite flavour.** `Law.MagmaLaw.not_termDefinableFrom_of_clone` with the
witness required to be finite and the conclusion strengthened accordingly: refuting
`TermDefinableFromFin` refutes `TermDefinableFrom` as well, by
`Law.MagmaLaw.termDefinableFin_of_termDefinable`. -/
theorem not_termDefinableFromFin_of_clone {G : Type} [Finite G] (M : Magma G)
    (hM : @satisfies _ G M L') {ι : Type*} {C : ι → Magma G} {i₁ i₂ : ι} {c : ι → ι → ι}
    (hC : M.IsCloneFamily C i₁ i₂ c) (hL : ∀ i, ¬ @satisfies _ G (C i) L) :
    ¬ L.TermDefinableFromFin L' := fun h ↦
  let ⟨_, hM', hd⟩ := h M hM
  let ⟨i, hi⟩ := hC.exists_eq hd
  hL i (hi ▸ hM')

/-- **The regular certificate.** If the regular operation `x ◇ y = x + h₀ (-x + y)` on a finite
group `G` satisfies `L'`, and *no* regular operation on `G` satisfies `L`, then `L` is not
term-definable from `L'` over finite magmas — hence not over all magmas either.

Both hypotheses are `Decidable`, the second being a quantifier over the function type `G → G`. This
is the entire interface: a certificate is an `h₀`, a source and a list of targets. -/
theorem not_termDefinableFromFin_of_transClone {G : Type} [AddGroup G] [Finite G] (h₀ : G → G)
    (hM : @satisfies _ G (Magma.transOp h₀) L')
    (hL : ∀ h : G → G, ¬ @satisfies _ G (Magma.transOp h) L) :
    ¬ L.TermDefinableFromFin L' :=
  not_termDefinableFromFin_of_clone _ hM (Magma.transOp_isCloneFamily h₀) hL

end Law.MagmaLaw
