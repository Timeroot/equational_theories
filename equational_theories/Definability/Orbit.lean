import equational_theories.Definability.Regular

/-!
# Clones indexed by representatives of the pairs under the endomorphisms

`Definability/Regular.lean` gets an unlistable clone family out of one special case: a group acting
on itself by translation. That action is *regular* — one orbit, trivial stabilizers — so an
operation invariant under it is determined by its values on a single row, and the family is indexed
by `G → G`.

Most symmetries are not regular, and most are not even invertible. What the clone conditions
actually need is far weaker than a group: the maps that move values around have only to be
*endomorphisms* of the model. So the index is a set of representatives of the pairs `(x, y)` under
whatever submonoid of `End M` is available, and the fewer representatives it takes to reach all of
`G × G`, the smaller the family. On `Fin 4` a fixed-point-free involution leaves eight orbits on
pairs, whereas the endomorphism monoid of a model with an idempotent diagonal gets down to six —
`4 ^ 6` operations instead of `4 ^ 8`.

This file states that in the form the certificates need, with no group in sight. The data is

* `rep : G → G → κ`, naming the representative that the pair `(x, y)` is reached from;
* `act x y : G → G`, the endomorphism carrying the value at that representative to the value at
  `(x, y)`;

and `Magma.RepData.decode i x y = act x y (i (rep x y))` turns an assignment `i : κ → G` of values to
representatives into an operation. Three side conditions make `decode` a clone family over a magma
`M`: each `act x y` is an endomorphism of `M`, and the two projections are decoded by the
assignments `i₁`, `i₂`. Composition is then *pointwise in the index*,
`c i j = fun k ↦ M.op (i k) (j k)`, with no table — the same phenomenon that makes
`Definability/Regular.lean` work, and for the same reason.

`Magma.transRepData` records that translation is the special case `κ = G`, `rep x y = -x + y`,
`act x y = (x + ·)`, so `Magma.transOp` is a `Magma.RepData.decode` on the nose.

Note the family is *larger* than the equivariant operations: an assignment whose values at two
representatives are not consistent with the maps between them still decodes to an operation, just
not to an equivariant one. That is harmless — a clone family only has to be a superset of the
clone — but it is what has to be refuted, so the certificates in `Definability/OrbitCover.lean`
quantify over all of `κ → G` and not over the equivariant operations.

The models are finite and the refutations are stated against `Law.MagmaLaw.TermDefinableFromFin`,
as in `Definability/Regular.lean`. As always with a clone argument, nothing is said about
first-order definability.
-/

open Law Law.MagmaLaw

namespace Magma

variable {G κ : Type}

/-- The data naming a set of representatives of the pairs: `rep x y` is the representative that
`(x, y)` is reached from, and `act x y` carries a value there to a value at `(x, y)`. -/
structure RepData (G κ : Type) where
  /-- The representative that the pair `(x, y)` is reached from. -/
  rep : G → G → κ
  /-- The map from the value at `rep x y` to the value at `(x, y)`. -/
  act : G → G → (G → G)

/-- The operation obtained by reading `i` as a table of values at the representatives. -/
@[implicit_reducible]
def RepData.decode (R : RepData G κ) (i : κ → G) : Magma G :=
  ⟨fun x y ↦ R.act x y (i (R.rep x y))⟩

@[simp]
theorem RepData.decode_op (R : RepData G κ) (i : κ → G) (x y : G) :
    (R.decode i).op x y = R.act x y (i (R.rep x y)) := rfl

/-- **The orbit clone family.** If every `act x y` is an endomorphism of `M` and the assignments
`i₁`, `i₂` decode to the two projections, then the decoded operations form a clone family for `M`,
indexed by `κ → G` and closed under a composition that is pointwise in the index. No enumeration
and no composition table. -/
theorem RepData.isCloneFamily (R : RepData G κ) (M : Magma G) (i₁ i₂ : κ → G)
    (hact : ∀ x y, M.IsEndo (R.act x y))
    (h₁ : ∀ x y, R.act x y (i₁ (R.rep x y)) = x)
    (h₂ : ∀ x y, R.act x y (i₂ (R.rep x y)) = y) :
    M.IsCloneFamily R.decode i₁ i₂ (fun i j k ↦ M.op (i k) (j k)) where
  fst := h₁
  snd := h₂
  comp i j x y := hact x y (i (R.rep x y)) (j (R.rep x y))

/-- Translation is the regular case: one orbit for every `-x + y`, moved into place by `x + ·`.
`Magma.transOp` of `Definability/Regular.lean` is this `decode`, definitionally. -/
def transRepData (G : Type) [AddGroup G] : RepData G G where
  rep x y := -x + y
  act x _ := (x + ·)

theorem transRepData_decode {G : Type} [AddGroup G] (h : G → G) :
    (transRepData G).decode h = transOp h := rfl

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- **The orbit certificate.** If the decoded operation `R.decode i₀` on a finite carrier satisfies
`L'`, if every `R.act x y` is an endomorphism of it, if `i₁` and `i₂` decode to the projections, and
if *no* decoded operation satisfies `L`, then `L` is not term-definable from `L'` over finite
magmas — hence not over all magmas either.

Every hypothesis is `Decidable` on a finite carrier: `hact` costs `|G| ^ 4`, `h₁` and `h₂` cost
`|G| ^ 2`, the source costs one law evaluation over `G`, and the target costs `|κ| ^ |G|` law
evaluations. Only the last is ever large. -/
theorem not_termDefinableFromFin_of_repData {G κ : Type} [Finite G] (R : Magma.RepData G κ)
    (i₀ i₁ i₂ : κ → G)
    (hact : ∀ x y, (R.decode i₀).IsEndo (R.act x y))
    (h₁ : ∀ x y, R.act x y (i₁ (R.rep x y)) = x)
    (h₂ : ∀ x y, R.act x y (i₂ (R.rep x y)) = y)
    (hM : @satisfies _ G (R.decode i₀) L')
    (hL : ∀ i : κ → G, ¬ @satisfies _ G (R.decode i) L) :
    ¬ L.TermDefinableFromFin L' :=
  not_termDefinableFromFin_of_clone _ hM (R.isCloneFamily _ i₁ i₂ hact h₁ h₂) hL

end Law.MagmaLaw
