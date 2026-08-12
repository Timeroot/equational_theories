import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.GroupTheory.Perm.Basic
import equational_theories.Definability.Basic

/-!
# Negative results for definability

`Definability/Basic.lean` sets up four preorders on magma laws (`TermStructuralFrom`,
`TermDefinableFrom`, `StructuralFrom`, `DefinableFrom`) and gives tools for proving that one law
*is* definable from another. This file gives tools for proving that one law is *not*.

All four notions have the same shape: if `L` is (term-)definable from `L'`, then **every** magma
`M` on a carrier `G` satisfying `L'` yields a *new* magma `M'` **on the same carrier `G`** which
satisfies `L`. So any property of the carrier that is forced by `L'` and forbidden by `L` refutes
definability. Two such properties are developed here.

* **Cardinality.** The carrier does not change at all, so if `L'` has a model of size `n` and `L`
  has none, `L` is not definable from `L'`: `Law.MagmaLaw.not_definableFrom_of_no_model`.
  (This is only useful for finite `n`, since every law has a countably infinite model.)

* **Symmetry.** Call `f : G → G` an *endomorphism* of `M` when `f (x ◇ y) = f x ◇ f y`
  (`Magma.IsEndo`); these form a submonoid `Magma.endos` of `Function.End G`, and the invertible
  ones form a subgroup `Magma.autos` of `Equiv.Perm G`. The new operation `M'` inherits the
  symmetries of `M`, so if no model of `L` on `G` has all the symmetries that `M` has, then `L` is
  not definable from `L'`.

  The two notions of definability behave differently here, which answers a natural question:

  - a **term**-definable operation is preserved by every endomorphism, invertible or not
    (`Magma.IsEndo.of_termDefinable`), because terms are preserved by homomorphisms;
  - a merely **first-order** definable operation is only preserved by *automorphisms*
    (`Magma.IsEndo.of_definable`), because first-order formulas are preserved by isomorphisms but
    not by arbitrary endomorphisms.

  So the non-invertible refinement refutes `TermDefinableFrom` only; to refute the full
  `DefinableFrom` one has to stick to bijections.

As an illustration, `Magma.isEndo_swap_iff` classifies the two-element magmas admitting the
nontrivial permutation of `Fin 2` as an automorphism: they are exactly the four "unary" operations
`x ◇ y = x`, `y`, `x + 1`, `y + 1`. (Note that XOR is *not* among them: `¬x` XOR `¬y` equals
`x` XOR `y`, not `¬(x XOR y)`. What XOR does have is the idempotent `0`, hence the constant
endomorphism at `0`; see `Magma.isEndo_const`.)
-/

open FirstOrder FirstOrder.Language
open Law Law.MagmaLaw

/-- Every function symbol of `MagmaLanguage` has arity `2`. -/
theorem MagmaLanguage.arity_eq_two {n : ℕ} (f : MagmaLanguage.Functions n) : n = 2 := by
  by_contra hn
  exact isEmptyElim (show Empty by simpa [MagmaLanguage, hn] using f)

namespace Magma

variable {G : Type*}

/-! ### Endomorphisms and automorphisms of a magma -/

/-- `M.IsEndo f` says that `f : G → G` commutes with the operation of the magma `M`, i.e. that `f`
is an endomorphism of `M`. Note that `f` is *not* required to be invertible. -/
def IsEndo (M : Magma G) (f : G → G) : Prop :=
  ∀ x y : G, f (M.op x y) = M.op (f x) (f y)

instance [Fintype G] [DecidableEq G] (M : Magma G) (f : G → G) : Decidable (M.IsEndo f) :=
  inferInstanceAs (Decidable (∀ _ _, _))

theorem isEndo_id (M : Magma G) : M.IsEndo id := fun _ _ ↦ rfl

theorem IsEndo.comp {M : Magma G} {f g : G → G} (hf : M.IsEndo f) (hg : M.IsEndo g) :
    M.IsEndo (f ∘ g) := fun x y ↦ by
  simp only [Function.comp_apply, hg x y, hf (g x) (g y)]

/-- The inverse of a bijective endomorphism is again an endomorphism. -/
theorem IsEndo.symm {M : Magma G} {e : G ≃ G} (he : M.IsEndo e) : M.IsEndo ⇑e.symm := fun x y ↦
  e.injective <| by rw [e.apply_symm_apply, he, e.apply_symm_apply, e.apply_symm_apply]

/-- Any constant map at an idempotent element is an endomorphism. This is the most common source
of *non-invertible* endomorphisms. -/
theorem isEndo_const {M : Magma G} {a : G} (ha : M.op a a = a) :
    M.IsEndo (Function.const G a) := fun _ _ ↦ ha.symm

/-- The endomorphisms of `M`, as a submonoid of the monoid `Function.End G` of all self-maps of
`G` under composition. -/
def endos (M : Magma G) : Submonoid (Function.End G) where
  carrier := {f | M.IsEndo f}
  one_mem' := M.isEndo_id
  mul_mem' := IsEndo.comp

@[simp]
theorem mem_endos {M : Magma G} {f : Function.End G} : f ∈ M.endos ↔ M.IsEndo f := Iff.rfl

/-- The automorphisms of `M`, as a subgroup of the permutation group of `G`. -/
def autos (M : Magma G) : Subgroup (Equiv.Perm G) where
  carrier := {e | M.IsEndo e}
  one_mem' := M.isEndo_id
  mul_mem' hf hg := IsEndo.comp hf hg
  inv_mem' he := IsEndo.symm he

@[simp]
theorem mem_autos {M : Magma G} {e : Equiv.Perm G} : e ∈ M.autos ↔ M.IsEndo ⇑e := Iff.rfl

end Magma

/-! ### Endomorphisms are preserved by term-definability -/

/-- Endomorphisms of a magma commute with the realization of any term in the language of magmas.
This is the usual "homomorphisms preserve terms", specialized to `MagmaLanguage`. -/
theorem FirstOrder.Language.Term.realize_isEndo {G : Type*} {M : Magma G} {f : G → G}
    (hf : M.IsEndo f) {α : Type*} (v : α → G) (t : MagmaLanguage.Term α) :
    f (@Term.realize _ _ M.FOStructure _ v t) = @Term.realize _ _ M.FOStructure _ (f ∘ v) t := by
  induction t with
  | var _ => rfl
  | func F ts ih =>
    obtain rfl := MagmaLanguage.arity_eq_two F
    simp only [Term.realize, Magma.FOStructure_funMap, Magma.FinArityOp]
    rw [hf, ih 0, ih 1]

/-- An operation that is *term*-definable from `M` inherits **all** the endomorphisms of `M`,
including the non-invertible ones. -/
theorem Magma.IsEndo.of_termDefinable {G : Type} {M M' : Magma G}
    (h : @Set.TermDefinable G ∅ MagmaLanguage M.FOStructure (Fin 2) M'.FinArityOp)
    {f : G → G} (hf : M.IsEndo f) : M'.IsEndo f := by
  letI := M.FOStructure
  rw [Set.termDefinable_empty_iff] at h
  obtain ⟨t, ht⟩ := h
  have key : ∀ v : Fin 2 → G, f (M'.FinArityOp v) = M'.FinArityOp (f ∘ v) := fun v ↦ by
    rw [ht]; exact Term.realize_isEndo hf v t
  exact fun x y ↦ key ![x, y]

/-- An operation that is first-order definable from `M` inherits the **automorphisms** of `M`.
Unlike `Magma.IsEndo.of_termDefinable` this really does need `e` to be invertible: a first-order
formula is preserved by isomorphisms, but not by arbitrary endomorphisms. -/
theorem Magma.IsEndo.of_definable {G : Type} {M M' : Magma G}
    (h : @Set.Definable G ∅ MagmaLanguage M.FOStructure (Option (Fin 2)) M'.Graph)
    {e : G ≃ G} (he : M.IsEndo e) : M'.IsEndo ⇑e := by
  letI := M.FOStructure
  obtain ⟨φ, hφ⟩ := h
  -- `e` is an automorphism of the first-order structure attached to `M`; there are no constants
  -- to preserve, since the parameter set is empty.
  let g : G ≃[MagmaLanguage[[(∅ : Set G)]]] G :=
    { toEquiv := e
      map_fun' := by
        rintro n (F | F) x
        · obtain rfl := MagmaLanguage.arity_eq_two F
          simp only [Magma.FOStructure_funMap']
          exact he _ _
        · exact isEmptyElim F
      map_rel' := by
        rintro n (R | R) x
        · exact (show Empty from R).elim
        · exact isEmptyElim R }
  intro x y
  -- The graph of `M'` is a definable set, so it is invariant under `g`.
  have hmem : (fun i ↦ Option.elim i (M'.op x y) ![x, y]) ∈ M'.Graph := rfl
  rw [hφ] at hmem
  have hmem' : (⇑g ∘ fun i ↦ Option.elim i (M'.op x y) ![x, y]) ∈ M'.Graph := by
    rw [hφ]; exact (StrongHomClass.realize_formula g φ).mpr hmem
  exact hmem'.symm

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-! ### The obstructions -/

/-- **Cardinality obstruction.** If `L'` has a model on the carrier `G` but `L` has none, then `L`
is not definable from `L'`. Since every law has a countably infinite model, this is only ever
useful for finite `G`. -/
theorem not_definableFrom_of_no_model {G : Type} (M : Magma G) (hM : @satisfies _ G M L')
    (hL : ∀ M' : Magma G, ¬ @satisfies _ G M' L) : ¬ L.DefinableFrom L' := fun h ↦
  let ⟨M', hM', _⟩ := h M hM
  hL M' hM'

/-- **Symmetry obstruction for term-definability**, in terms of a single endomorphism. If `L'` has
a model `M` on `G` with `f` as an endomorphism, but no model of `L` on `G` has `f` as an
endomorphism, then `L` is not term-definable from `L'`. `f` need not be invertible. -/
theorem not_termDefinableFrom_of_isEndo {G : Type} (M : Magma G) (hM : @satisfies _ G M L')
    {f : G → G} (hf : M.IsEndo f) (hL : ∀ M' : Magma G, @satisfies _ G M' L → ¬ M'.IsEndo f) :
    ¬ L.TermDefinableFrom L' := fun h ↦
  let ⟨M', hM', hd⟩ := h M hM
  hL M' hM' (hf.of_termDefinable hd)

/-- **Symmetry obstruction for term-definability**, in terms of the whole endomorphism monoid: the
model produced for `L` has at least the symmetries that the given model of `L'` has. -/
theorem not_termDefinableFrom_of_endos {G : Type} (M : Magma G) (hM : @satisfies _ G M L')
    (hL : ∀ M' : Magma G, @satisfies _ G M' L → ¬ M.endos ≤ M'.endos) :
    ¬ L.TermDefinableFrom L' := fun h ↦
  let ⟨M', hM', hd⟩ := h M hM
  hL M' hM' fun _ hf ↦ hf.of_termDefinable hd

/-- **Symmetry obstruction for first-order definability**, in terms of a single automorphism. -/
theorem not_definableFrom_of_isAuto {G : Type} (M : Magma G) (hM : @satisfies _ G M L')
    {e : G ≃ G} (he : M.IsEndo e) (hL : ∀ M' : Magma G, @satisfies _ G M' L → ¬ M'.IsEndo ⇑e) :
    ¬ L.DefinableFrom L' := fun h ↦
  let ⟨M', hM', hd⟩ := h M hM
  hL M' hM' (he.of_definable hd)

/-- **Symmetry obstruction for first-order definability**, in terms of the whole automorphism
group: the model produced for `L` has at least the symmetries that the given model of `L'` has. -/
theorem not_definableFrom_of_autos {G : Type} (M : Magma G) (hM : @satisfies _ G M L')
    (hL : ∀ M' : Magma G, @satisfies _ G M' L → ¬ M.autos ≤ M'.autos) :
    ¬ L.DefinableFrom L' := fun h ↦
  let ⟨M', hM', hd⟩ := h M hM
  hL M' hM' fun _ he ↦ he.of_definable hd

/-- Specialization of `not_termDefinableFrom_of_isEndo` to the constant endomorphism at an
idempotent: idempotents of `M` remain idempotent for any term-definable operation. -/
theorem not_termDefinableFrom_of_idempotent {G : Type} (M : Magma G) (hM : @satisfies _ G M L')
    {a : G} (ha : M.op a a = a)
    (hL : ∀ M' : Magma G, @satisfies _ G M' L → M'.op a a ≠ a) :
    ¬ L.TermDefinableFrom L' :=
  not_termDefinableFrom_of_isEndo M hM (Magma.isEndo_const ha)
    fun M' hM' hc ↦ hL M' hM' (hc a a).symm

/-! ### Transferring negative results down the hierarchy

`DefinableFrom` is the weakest of the four relations, so refuting it refutes all of them. -/

theorem not_termDefinableFrom_of_not_definableFrom (h : ¬ L.DefinableFrom L') :
    ¬ L.TermDefinableFrom L' := fun h' ↦ h (definable_of_termDefinable h')

theorem not_structuralFrom_of_not_definableFrom (h : ¬ L.DefinableFrom L') :
    ¬ L.StructuralFrom L' := fun h' ↦ h (definable_of_structural h')

theorem not_termStructuralFrom_of_not_termDefinableFrom (h : ¬ L.TermDefinableFrom L') :
    ¬ L.TermStructuralFrom L' := fun h' ↦ h (termDefinable_of_termStructural h')

theorem not_implies_of_not_termDefinableFrom (h : ¬ L.TermDefinableFrom L') : ¬ L'.implies L :=
  fun h' ↦ h (termDefinable_of_termStructural (termStructural_of_implies h'))

end Law.MagmaLaw

/-! ### The two-element case

On `Fin 2` there is only one nontrivial permutation, `x ↦ x + 1`, and it is an automorphism of
exactly four of the sixteen binary operations. -/

/-- The nontrivial permutation of `Fin 2`. -/
abbrev Fin.swap2 : Equiv.Perm (Fin 2) := Equiv.addRight 1

@[simp]
theorem Fin.swap2_apply (x : Fin 2) : Fin.swap2 x = x + 1 := rfl

/-- A binary operation on `Fin 2` admits the nontrivial permutation as an automorphism if and only
if it is one of the four operations that ignore one of their arguments and either copy or negate
the other. -/
theorem Magma.isEndo_swap_iff (op : Fin 2 → Fin 2 → Fin 2) :
    (Magma.mk op).IsEndo ⇑Fin.swap2 ↔
      op = (fun x _ ↦ x) ∨ op = (fun _ y ↦ y) ∨
        op = (fun x _ ↦ x + 1) ∨ op = (fun _ y ↦ y + 1) := by
  revert op
  decide

/-- The two-element instance of the symmetry obstruction, in the form that is convenient to check
by `decide`: if `L'` has a two-element model with a nontrivial automorphism, then any law
definable from `L'` is satisfied by one of four explicit two-element magmas. -/
theorem Law.MagmaLaw.exists_fin2_model_of_definableFrom {β : Type*} {L L' : Law.MagmaLaw β}
    (M : Magma (Fin 2)) (hM : satisfies (Fin 2) L') (hswap : M.IsEndo ⇑Fin.swap2)
    (h : L.DefinableFrom L') :
    ∃ op : Fin 2 → Fin 2 → Fin 2,
      (op = (fun x _ ↦ x) ∨ op = (fun _ y ↦ y) ∨
        op = (fun x _ ↦ x + 1) ∨ op = (fun _ y ↦ y + 1)) ∧
      @satisfies _ (Fin 2) (Magma.mk op) L := by
  obtain ⟨M', hM', hd⟩ := h M hM
  exact ⟨M'.op, (Magma.isEndo_swap_iff M'.op).mp (hswap.of_definable hd), hM'⟩

/-! ### Worked examples

Both obstructions in action, on laws written out by hand so that this file stays independent of
the generated `Equations` files. -/

namespace Law.MagmaLaw

/-- **Cardinality.** The law `x ≃ y` holds only in subsingletons, so it is not definable from the
trivial law `x ≃ x`, which every magma satisfies. -/
theorem not_definableFrom_of_eq_law :
    ¬ (Lf 0 ≃ Lf 1 : NatMagmaLaw).DefinableFrom (Lf 0 ≃ Lf 0) := by
  refine not_definableFrom_of_no_model (G := Fin 2) (Magma.mk fun x _ ↦ x) (fun _ ↦ rfl) ?_
  intro M' h
  have key : (0 : Fin 2) = 1 := h fun n ↦ if n = 0 then 0 else 1
  exact absurd key (by decide)

/-- **Symmetry.** Commutativity `x ◇ y ≃ y ◇ x` is not definable from the left-projection law
`x ◇ y ≃ x`. Indeed left projection on `Fin 2` admits the nontrivial permutation as an
automorphism, and by `Magma.isEndo_swap_iff` the only two-element magmas with that automorphism
ignore one of their arguments — so none of them is commutative. -/
theorem comm_not_definableFrom_leftProjection :
    ¬ (Lf 0 ⋆ Lf 1 ≃ Lf 1 ⋆ Lf 0 : NatMagmaLaw).DefinableFrom (Lf 0 ⋆ Lf 1 ≃ Lf 0) := by
  refine not_definableFrom_of_isAuto (G := Fin 2) (Magma.mk fun x _ ↦ x) (fun _ ↦ rfl)
    (e := Fin.swap2) (by decide) ?_
  intro M' hcomm hendo
  have key : M'.op 0 1 = M'.op 1 0 := hcomm fun n ↦ if n = 0 then 0 else 1
  rcases (Magma.isEndo_swap_iff M'.op).mp hendo with h | h | h | h <;>
    rw [h] at key <;> exact absurd key (by decide)

end Law.MagmaLaw
