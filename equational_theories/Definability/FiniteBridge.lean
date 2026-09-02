import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Set
import equational_theories.Definability.FiniteFlavour

/-!
# On a finite carrier, `Aut`-invariant is the same as `∅`-definable

Every refutation in this directory uses one direction of this: a `∅`-definable set is fixed by
every automorphism, so exhibiting an automorphism that moves a candidate operation kills it. The
converse holds too as soon as the carrier is finite, and it is the direction that *builds* things.
It is what makes the finite flavour of `StructuralOnMagma` purely combinatorial:

    StructuralOnMagma L M  ↔  ∃ M' on the same carrier, M' ⊨ L and Aut M' = Aut M     (`M` finite)

with no formula anywhere in sight.

The formula that witnesses it quantifies over a block of binders indexed by the carrier itself, so
a valuation of the block *is* a map `G → G`; `autF` says that map is an injective endomorphism --
a bijection, since `G` is finite -- and `memF` says the free variables are its image of some member
of `S`. Together they define the `Aut`-closure of `S`, which is `S`.

`Mathlib.ModelTheory.Syntax` already has the two combinators this needs: `Formula.iExs`, which
binds a whole finite block at once, and `Formula.iInf`/`iSup` over a finite index. Without them the
formula would have to be built by recursion on an enumeration of the carrier.
-/

open FirstOrder FirstOrder.Language

namespace Magma

section bridge

local instance instFOStructure' {G : Type} [M : Magma G] : MagmaLanguage.Structure G := M.FOStructure

variable {G : Type}

/-- `a ⋆ b` as a term of the magma language over an empty constant set. -/
def apT (G : Type) {γ : Type} (a b : (MagmaLanguage[[(∅ : Set G)]]).Term γ) :
    (MagmaLanguage[[(∅ : Set G)]]).Term γ :=
  Functions.apply₂ (L := MagmaLanguage[[(∅ : Set G)]]) (Sum.inl ()) a b

@[simp]
theorem realize_apT [N : Magma G] {γ : Type} (v : γ → G)
    (a b : (MagmaLanguage[[(∅ : Set G)]]).Term γ) :
    Term.realize v (apT G a b) = N.op (Term.realize v a) (Term.realize v b) := by
  simp only [apT, Term.realize_functions_apply₂, Magma.FOStructure_funMap']
  rfl

/-- The binder block, indexed by the carrier, names an injective endomorphism of `M`. -/
noncomputable def autF (α : Type) [Finite G] (M : Magma G) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (α ⊕ G) :=
  Formula.iInf (fun p : G × G =>
      Term.equal (apT G (Term.var (Sum.inr p.1)) (Term.var (Sum.inr p.2)))
        (Term.var (Sum.inr (M.op p.1 p.2)))) ⊓
    Formula.iInf (fun p : {p : G × G // p.1 ≠ p.2} =>
      ∼(Term.equal (Term.var (Sum.inr p.1.1)) (Term.var (Sum.inr p.1.2))))

/-- The free variables are the binder block's image of some member of `S`. -/
noncomputable def memF [Finite G] {α : Type} [Finite α] (S : Set (α → G)) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula (α ⊕ G) :=
  Formula.iSup (fun w : {w : α → G // w ∈ S} =>
    Formula.iInf (fun a : α =>
      Term.equal (Term.var (Sum.inl a)) (Term.var (Sum.inr (w.1 a)))))

/-- `∃ σ ∈ Aut M, x ∈ σ '' S`, which for `S` invariant is `S`. -/
noncomputable def invF [Finite G] {α : Type} [Finite α] (M : Magma G) (S : Set (α → G)) :
    (MagmaLanguage[[(∅ : Set G)]]).Formula α :=
  Formula.iExs G (autF α M ⊓ memF S)

/-- **The bridge.** On a finite carrier every set of tuples fixed by every automorphism of `M` is
`∅`-definable in `M`. -/
theorem definable_of_aut_invariant [Finite G] {α : Type} [Finite α] (M : Magma G)
    (S : Set (α → G))
    (hS : ∀ σ : G → G, Function.Bijective σ →
      (∀ a b : G, σ (M.op a b) = M.op (σ a) (σ b)) → ∀ v ∈ S, σ ∘ v ∈ S) :
    @Set.Definable _ (∅ : Set G) MagmaLanguage M.FOStructure _ S := by
  classical
  refine ⟨invF M S, Set.ext fun v ↦ ?_⟩
  show v ∈ S ↔ _
  simp only [Set.mem_setOf_eq, invF, autF, memF, Formula.realize_iExs, Formula.realize_inf,
    Formula.realize_iInf, Formula.realize_iSup, Formula.realize_equal, Term.realize_var, @realize_apT _ M, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro hv
    exact ⟨id, ⟨fun p ↦ rfl, fun p : {p : G × G // p.1 ≠ p.2} ↦ p.2⟩, ⟨v, hv⟩, fun a ↦ rfl⟩
  · rintro ⟨i, ⟨hhom, hinj⟩, ⟨w, hw⟩, hwv⟩
    have hi : Function.Injective i := by
      intro a b hab
      by_contra hne
      exact hinj ⟨(a, b), hne⟩ hab
    have hv : v = i ∘ w := funext fun a ↦ hwv a
    rw [hv]
    exact hS i (Finite.injective_iff_bijective.mp hi) (fun a b ↦ (hhom (a, b)).symm) w hw

end bridge

end Magma
