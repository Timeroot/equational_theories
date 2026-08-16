import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FinCases
import equational_theories.Definability.Basic
import equational_theories.Equations.All

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

To use the symmetry obstruction one has to know *all* magmas on `G` with a given symmetry, so that
the "no model of `L` has it" side can be checked mechanically. Demanding a symmetry cuts the search
space down enormously, and the classifications are all elementary:

* `Magma.isEndo_swap_iff`: the two-element magmas admitting the nontrivial permutation of `Fin 2`
  as an automorphism are exactly the four "unary" operations `x ◇ y = x`, `y`, `x + 1`, `y + 1`.
  (Note that XOR is *not* among them: `¬x` XOR `¬y` equals `x` XOR `y`, not `¬(x XOR y)`. What XOR
  does have is the idempotent `0`, hence the constant endomorphism at `0`; see
  `Magma.isEndo_const`.)
* `Magma.op_eq_of_isEndo_add_one`: a magma on `Fin n` admitting the cyclic shift `x ↦ x + 1` as an
  automorphism is determined by its first row, `x ◇ y = 0 ◇ (y - x) + x`. So there are `n ^ n` of
  them instead of `n ^ (n ^ 2)`: `27` rather than `19683` when `n = 3`.
* `Magma.op_eq_of_isEndo_add_one_neg`: adding the reflection `x ↦ -x` to the cyclic shift leaves
  only the `3` affine operations `x ◇ y = c * (y - x) + x` on `Fin 3`.
* `Magma.op_eq_reflOp3`: the reflection alone leaves the `81` operations `Magma.reflOp3 a b c d`.
* `Magma.op_eq_of_isEndo_add_one_double`: likewise on `Fin 5`, the cyclic shift together with
  doubling — which generate the Frobenius group `F₂₀ = AGL(1, 5)` — leave only the `5` affine
  operations `x ◇ y = c * (y - x) + x`.

Finally, `Law.MagmaLaw.definableFrom_iff_implies_of_op_irrelevant` handles the laws that constrain
only the *carrier* and not the operation. The one such law of interest is equation 2, `x = y`,
which says that the carrier is a subsingleton; `Law2_definableFrom_iff` records that equation 2 is
definable from `L'` exactly when `L'` implies it, and `definableFrom_Law2` that everything is
definable from equation 2. This settles the whole row and column of equation 2 in the definability
graph, including entries no finiteness argument can reach.
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

/-- The cardinality obstruction on `Fin n`, phrased over raw operations rather than over magma
structures so that the hypothesis on `L` is `Decidable`. This is only practical for `n = 2`: there
are already `19683` operations on `Fin 3`. -/
theorem not_definableFrom_of_no_fin_model {n : ℕ} (M : Magma (Fin n)) (hM : satisfies (Fin n) L')
    (hL : ∀ op : Fin n → Fin n → Fin n, ¬ @satisfies _ (Fin n) (Magma.mk op) L) :
    ¬ L.DefinableFrom L' :=
  not_definableFrom_of_no_model M hM fun M' ↦ hL M'.op

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

/-- **Laws about the carrier alone.** Definability never changes the carrier, so if whether `L`
holds does not depend on the operation, then `L` is definable from `L'` precisely when `L'` already
implies `L`. Both directions are worth having: this is simultaneously a source of negative results
and a source of positive ones. -/
theorem definableFrom_iff_implies_of_op_irrelevant
    (hL : ∀ (G : Type) (M₁ M₂ : Magma G), @satisfies _ G M₁ L → @satisfies _ G M₂ L) :
    L.DefinableFrom L' ↔ L'.implies L := by
  refine ⟨fun h G M hM ↦ ?_, fun h ↦ definable_of_termDefinable
    (termDefinable_of_termStructural (termStructural_of_implies h))⟩
  obtain ⟨M', hM', -⟩ := h M hM
  exact hL G M' M hM'

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

/-! ### Cyclic symmetry

A magma on `Fin n` whose automorphisms include the cyclic shift `x ↦ x + 1` is determined by a
single function `Fin n → Fin n`, namely its first row. -/

namespace Magma

open Fin.NatCast in
/-- If the cyclic shift `x ↦ x + 1` is an endomorphism of `M`, then so is `x ↦ x + k`. -/
theorem op_add_natCast_of_isEndo_add_one {n : ℕ} [NeZero n] {M : Magma (Fin n)}
    (h : M.IsEndo (· + 1)) (k : ℕ) (x y : Fin n) :
    M.op (x + (k : Fin n)) (y + (k : Fin n)) = M.op x y + (k : Fin n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_add_one, ← add_assoc, ← add_assoc, ← h, ih]
    simp [add_assoc]

/-- A magma on `Fin n` admitting the cyclic shift as an automorphism is determined by its first
row: every entry is a shift of an entry of that row. -/
theorem op_eq_of_isEndo_add_one {n : ℕ} [NeZero n] {M : Magma (Fin n)}
    (h : M.IsEndo (· + 1)) (x y : Fin n) : M.op x y = M.op 0 (y - x) + x := by
  have := op_add_natCast_of_isEndo_add_one h x.val 0 (y - x)
  simpa using this

/-- On `Fin 3`, a magma admitting both the cyclic shift and the reflection `x ↦ -x` is *affine*:
its first row is linear, so the whole operation is `x ◇ y = c * (y - x) + x`. -/
theorem op_eq_of_isEndo_add_one_neg {M : Magma (Fin 3)} (h₁ : M.IsEndo (· + 1))
    (h₂ : M.IsEndo (fun x ↦ -x)) (x y : Fin 3) : M.op x y = M.op 0 1 * (y - x) + x := by
  have hodd : ∀ t : Fin 3, M.op 0 (-t) = -(M.op 0 t) := fun t ↦ by
    have := h₂ 0 t; simpa using this.symm
  have hz : M.op 0 0 = 0 := by
    have h00 := hodd 0
    simp only [neg_zero] at h00
    revert h00
    generalize M.op 0 0 = a
    revert a
    decide
  rw [op_eq_of_isEndo_add_one h₁]
  congr 1
  generalize y - x = t
  fin_cases t
  · simpa using hz
  · simp
  · show M.op 0 2 = M.op 0 1 * 2
    rw [show (2 : Fin 3) = -1 by decide, hodd 1, mul_neg_one]

/-- Doubling, `x ↦ 2 * x`, as a permutation of `Fin 5`; its inverse is tripling. Together with the
cyclic shift it generates the Frobenius group `F₂₀ = AGL(1, 5)`, the full group of affine maps of
`Fin 5`. -/
def _root_.Fin.double5 : Equiv.Perm (Fin 5) where
  toFun x := 2 * x
  invFun x := 3 * x
  left_inv := by decide
  right_inv := by decide

@[simp]
theorem _root_.Fin.double5_apply (x : Fin 5) : Fin.double5 x = 2 * x := rfl

/-- On `Fin 5`, a magma admitting both the cyclic shift and doubling — equivalently, all of
`F₂₀` — is *affine*: its first row is linear, so the whole operation is `x ◇ y = c * (y - x) + x`.

Doubling generates the multiplicative group of `Fin 5`, so the first row `t ↦ 0 ◇ t` satisfies
`0 ◇ 2t = 2 * (0 ◇ t)` and is therefore determined by `c = 0 ◇ 1`. -/
theorem op_eq_of_isEndo_add_one_double {M : Magma (Fin 5)} (h₁ : M.IsEndo (· + 1))
    (h₂ : M.IsEndo ⇑Fin.double5) (x y : Fin 5) : M.op x y = M.op 0 1 * (y - x) + x := by
  have hdbl : ∀ t : Fin 5, M.op 0 (2 * t) = 2 * M.op 0 t := fun t ↦ by
    have := h₂ 0 t; simpa using this.symm
  have hz : M.op 0 0 = 0 := by
    have h00 := hdbl 0
    simp only [mul_zero] at h00
    revert h00
    generalize M.op 0 0 = a
    revert a
    decide
  have e2 : M.op 0 2 = M.op 0 1 * 2 := by
    have h := hdbl 1
    rw [show (2 : Fin 5) * 1 = 2 from rfl] at h
    rw [h]
    generalize M.op 0 1 = c
    revert c
    decide
  have e4 : M.op 0 4 = M.op 0 1 * 4 := by
    have h := hdbl 2
    rw [show (2 : Fin 5) * 2 = 4 from rfl, e2] at h
    rw [h]
    generalize M.op 0 1 = c
    revert c
    decide
  have e3 : M.op 0 3 = M.op 0 1 * 3 := by
    have h := hdbl 4
    rw [show (2 : Fin 5) * 4 = 3 from rfl, e4] at h
    rw [h]
    generalize M.op 0 1 = c
    revert c
    decide
  rw [op_eq_of_isEndo_add_one h₁]
  congr 1
  generalize y - x = t
  fin_cases t
  · simpa using hz
  · simp
  · exact e2
  · exact e3
  · exact e4

/-- Tripling, `x ↦ 3 * x`, as a permutation of `Fin 7`; its inverse is multiplication by `5`.
`3` is a primitive root mod `7`, so together with the cyclic shift this generates the Frobenius
group `F₄₂ = AGL(1, 7)`, the full group of affine maps of `Fin 7`. -/
def _root_.Fin.triple7 : Equiv.Perm (Fin 7) where
  toFun x := 3 * x
  invFun x := 5 * x
  left_inv := by decide
  right_inv := by decide

@[simp]
theorem _root_.Fin.triple7_apply (x : Fin 7) : Fin.triple7 x = 3 * x := rfl

/-- On `Fin 7`, a magma admitting both the cyclic shift and tripling — equivalently, all of
`F₄₂` — is *affine*: its first row is linear, so the whole operation is `x ◇ y = c * (y - x) + x`.

Tripling generates the multiplicative group of `Fin 7`, so the first row `t ↦ 0 ◇ t` satisfies
`0 ◇ 3t = 3 * (0 ◇ t)` and is therefore determined by `c = 0 ◇ 1`, along the orbit
`1 → 3 → 2 → 6 → 4 → 5 → 1`. -/
theorem op_eq_of_isEndo_add_one_triple {M : Magma (Fin 7)} (h₁ : M.IsEndo (· + 1))
    (h₂ : M.IsEndo ⇑Fin.triple7) (x y : Fin 7) : M.op x y = M.op 0 1 * (y - x) + x := by
  have htpl : ∀ t : Fin 7, M.op 0 (3 * t) = 3 * M.op 0 t := fun t ↦ by
    have := h₂ 0 t; simpa using this.symm
  have hz : M.op 0 0 = 0 := by
    have h00 := htpl 0
    simp only [mul_zero] at h00
    revert h00
    generalize M.op 0 0 = a
    revert a
    decide
  have e3 : M.op 0 3 = M.op 0 1 * 3 := by
    have h := htpl 1
    rw [show (3 : Fin 7) * 1 = 3 from rfl] at h
    rw [h]
    generalize M.op 0 1 = c
    revert c
    decide
  have e2 : M.op 0 2 = M.op 0 1 * 2 := by
    have h := htpl 3
    rw [show (3 : Fin 7) * 3 = 2 from rfl, e3] at h
    rw [h]
    generalize M.op 0 1 = c
    revert c
    decide
  have e6 : M.op 0 6 = M.op 0 1 * 6 := by
    have h := htpl 2
    rw [show (3 : Fin 7) * 2 = 6 from rfl, e2] at h
    rw [h]
    generalize M.op 0 1 = c
    revert c
    decide
  have e4 : M.op 0 4 = M.op 0 1 * 4 := by
    have h := htpl 6
    rw [show (3 : Fin 7) * 6 = 4 from rfl, e6] at h
    rw [h]
    generalize M.op 0 1 = c
    revert c
    decide
  have e5 : M.op 0 5 = M.op 0 1 * 5 := by
    have h := htpl 4
    rw [show (3 : Fin 7) * 4 = 5 from rfl, e4] at h
    rw [h]
    generalize M.op 0 1 = c
    revert c
    decide
  rw [op_eq_of_isEndo_add_one h₁]
  congr 1
  generalize y - x = t
  fin_cases t
  · simpa using hz
  · simp
  · exact e2
  · exact e3
  · exact e4
  · exact e5
  · exact e6

/-- The Klein four-group structure on `Fin 4`, i.e. bitwise xor. Its three nontrivial translations
are the double transpositions `(0 1)(2 3)`, `(0 2)(1 3)` and `(0 3)(1 2)`. -/
def _root_.Fin.xor4 : Fin 4 → Fin 4 → Fin 4
  | 0, y => y
  | 1, 0 => 1 | 1, 1 => 0 | 1, 2 => 3 | 1, 3 => 2
  | 2, 0 => 2 | 2, 1 => 3 | 2, 2 => 0 | 2, 3 => 1
  | 3, 0 => 3 | 3, 1 => 2 | 3, 2 => 1 | 3, 3 => 0

theorem _root_.Fin.xor4_self (a b : Fin 4) : Fin.xor4 a (Fin.xor4 a b) = b := by
  revert a b; decide

/-- Xor with `a`, as a permutation of `Fin 4`; it is its own inverse. -/
def _root_.Fin.xorPerm4 (a : Fin 4) : Equiv.Perm (Fin 4) where
  toFun := Fin.xor4 a
  invFun := Fin.xor4 a
  left_inv := Fin.xor4_self a
  right_inv := Fin.xor4_self a

@[simp]
theorem _root_.Fin.xorPerm4_apply (a b : Fin 4) : Fin.xorPerm4 a b = Fin.xor4 a b := rfl

/-- The rotation `1 ↦ 2 ↦ 3 ↦ 1` of `Fin 4`. It fixes `0` and permutes the three nonzero elements
cyclically; together with `Fin.xor4` it generates the alternating group `A₄`, which acts sharply
transitively on the twelve ordered pairs of distinct elements. -/
def _root_.Fin.rot4 : Equiv.Perm (Fin 4) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by decide
  right_inv := by decide

@[simp]
theorem _root_.Fin.rot4_zero : Fin.rot4 0 = 0 := rfl

/-- The first row of an `A₄`-invariant operation on `Fin 4`: it is `0` at `0`, since the stabilizer
of `0` in `A₄` fixes nothing else, and elsewhere it is the `Fin.rot4`-orbit of `c = 0 ◇ 1`. -/
def a4Row (c : Fin 4) : Fin 4 → Fin 4
  | 0 => 0
  | 1 => c
  | 2 => Fin.rot4 c
  | 3 => Fin.rot4 (Fin.rot4 c)

/-- The `4` operations on `Fin 4` invariant under the alternating group `A₄`, parametrized by
`c = 0 ◇ 1`. Two of them are the projections `x ◇ y = x` (at `c = 0`) and `x ◇ y = y` (at `c = 1`);
the other two send a pair of distinct elements to one of the two remaining elements, the choice
being made by orientation. -/
def a4Op (c : Fin 4) (x y : Fin 4) : Fin 4 := Fin.xor4 x (a4Row c (Fin.xor4 x y))

/-- Every magma on `Fin 4` admitting the alternating group as automorphisms is one of the `4`
magmas `Magma.a4Op c`. The Klein subgroup acts regularly, which reduces the operation to its first
row, and the rotation then pins that row down to the single value `c = 0 ◇ 1`. -/
theorem op_eq_a4Op {M : Magma (Fin 4)} (h₁ : M.IsEndo (Fin.xor4 1)) (h₂ : M.IsEndo (Fin.xor4 2))
    (hr : M.IsEndo ⇑Fin.rot4) : M.op = a4Op (M.op 0 1) := by
  have h₃ : M.IsEndo (Fin.xor4 3) := by
    have e : Fin.xor4 3 = Fin.xor4 1 ∘ Fin.xor4 2 := by funext z; revert z; decide
    rw [e]; exact h₁.comp h₂
  have hz : M.op 0 0 = 0 := by
    have h := hr 0 0
    rw [Fin.rot4_zero] at h
    revert h
    generalize M.op 0 0 = a
    revert a
    decide
  have e2 : M.op 0 2 = Fin.rot4 (M.op 0 1) := by
    have h := hr 0 1
    rw [Fin.rot4_zero, show Fin.rot4 1 = 2 from rfl] at h
    exact h.symm
  have e3 : M.op 0 3 = Fin.rot4 (M.op 0 2) := by
    have h := hr 0 2
    rw [Fin.rot4_zero, show Fin.rot4 2 = 3 from rfl] at h
    exact h.symm
  have step : ∀ a : Fin 4, M.IsEndo (Fin.xor4 a) → ∀ y : Fin 4,
      M.op (Fin.xor4 a 0) y = Fin.xor4 a (M.op 0 (Fin.xor4 a y)) := fun a ha y ↦ by
    have h := ha 0 (Fin.xor4 a y)
    rw [Fin.xor4_self] at h
    exact h.symm
  have key : ∀ x y : Fin 4, M.op x y = Fin.xor4 x (M.op 0 (Fin.xor4 x y)) := by
    intro x y
    fin_cases x
    exacts [rfl, step 1 h₁ y, step 2 h₂ y, step 3 h₃ y]
  funext x y
  rw [key x y]
  show Fin.xor4 x (M.op 0 (Fin.xor4 x y)) = Fin.xor4 x (a4Row (M.op 0 1) (Fin.xor4 x y))
  congr 1
  generalize Fin.xor4 x y = t
  fin_cases t
  exacts [hz, rfl, e2, e3.trans (congrArg _ e2)]

/-- Addition in `GF(8) = 𝔽₂[X]/(X³ + X + 1)`, transported to `Fin 8` by reading `i` in binary as
the polynomial with those coefficients; concretely, bitwise xor. -/
def _root_.Fin.xor8 : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7],
    ![1, 0, 3, 2, 5, 4, 7, 6],
    ![2, 3, 0, 1, 6, 7, 4, 5],
    ![3, 2, 1, 0, 7, 6, 5, 4],
    ![4, 5, 6, 7, 0, 1, 2, 3],
    ![5, 4, 7, 6, 1, 0, 3, 2],
    ![6, 7, 4, 5, 2, 3, 0, 1],
    ![7, 6, 5, 4, 3, 2, 1, 0] ]

theorem _root_.Fin.xor8_self (a b : Fin 8) : Fin.xor8 a (Fin.xor8 a b) = b := by revert a b; decide

/-- Translation by `a` in `GF(8)`, as a permutation of `Fin 8`; it is its own inverse. -/
def _root_.Fin.xorPerm8 (a : Fin 8) : Equiv.Perm (Fin 8) where
  toFun := Fin.xor8 a
  invFun := Fin.xor8 a
  left_inv := Fin.xor8_self a
  right_inv := Fin.xor8_self a

@[simp]
theorem _root_.Fin.xorPerm8_apply (a b : Fin 8) : Fin.xorPerm8 a b = Fin.xor8 a b := rfl

/-- Multiplication in `GF(8) = 𝔽₂[X]/(X³ + X + 1)`, transported to `Fin 8` as in `Fin.xor8`. -/
def _root_.Fin.gf8 : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 2, 4, 6, 3, 1, 7, 5],
    ![0, 3, 6, 5, 7, 4, 1, 2],
    ![0, 4, 3, 7, 6, 2, 5, 1],
    ![0, 5, 1, 4, 2, 7, 3, 6],
    ![0, 6, 7, 1, 5, 3, 2, 4],
    ![0, 7, 5, 2, 1, 6, 4, 3] ]

@[simp]
theorem _root_.Fin.gf8_zero_right (a : Fin 8) : Fin.gf8 a 0 = 0 := by revert a; decide

@[simp]
theorem _root_.Fin.gf8_one_right (a : Fin 8) : Fin.gf8 a 1 = a := by revert a; decide

/-- Multiplication by `X`, a generator of `GF(8)ˣ`, as a permutation of `Fin 8`; its inverse is
multiplication by `X² + 1`. Together with the translations `Fin.xorPerm8` it generates the group
`AGL(1, 8)` of all affine maps of `GF(8)`. -/
def _root_.Fin.double8 : Equiv.Perm (Fin 8) where
  toFun := Fin.gf8 2
  invFun := Fin.gf8 5
  left_inv := by decide
  right_inv := by decide

@[simp]
theorem _root_.Fin.double8_apply (x : Fin 8) : Fin.double8 x = Fin.gf8 2 x := rfl

/-- The `8` operations on `Fin 8` admitting all of `AGL(1, 8)` as automorphisms: the affine maps
`x ◇ y = x + c * (y - x)` of `GF(8)`, in which `-` and `+` are both `Fin.xor8`.

Spelled out as tables rather than as `Fin.xor8 x (Fin.gf8 c (Fin.xor8 x y))`, which is what
`Magma.a8Op_eq` says it is: the certificate tables of `Definability/Certs/` evaluate this operation
`8 ^ 4` times per equation, and one table lookup is a good deal cheaper than three. -/
@[implicit_reducible]
def a8Op : Fin 8 → Fin 8 → Fin 8 → Fin 8 := ![
  ![![0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 1, 1, 1, 1, 1],
    ![2, 2, 2, 2, 2, 2, 2, 2],
    ![3, 3, 3, 3, 3, 3, 3, 3],
    ![4, 4, 4, 4, 4, 4, 4, 4],
    ![5, 5, 5, 5, 5, 5, 5, 5],
    ![6, 6, 6, 6, 6, 6, 6, 6],
    ![7, 7, 7, 7, 7, 7, 7, 7] ],
  ![![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![0, 1, 2, 3, 4, 5, 6, 7] ],
  ![![0, 2, 4, 6, 3, 1, 7, 5],
    ![3, 1, 7, 5, 0, 2, 4, 6],
    ![6, 4, 2, 0, 5, 7, 1, 3],
    ![5, 7, 1, 3, 6, 4, 2, 0],
    ![7, 5, 3, 1, 4, 6, 0, 2],
    ![4, 6, 0, 2, 7, 5, 3, 1],
    ![1, 3, 5, 7, 2, 0, 6, 4],
    ![2, 0, 6, 4, 1, 3, 5, 7] ],
  ![![0, 3, 6, 5, 7, 4, 1, 2],
    ![2, 1, 4, 7, 5, 6, 3, 0],
    ![4, 7, 2, 1, 3, 0, 5, 6],
    ![6, 5, 0, 3, 1, 2, 7, 4],
    ![3, 0, 5, 6, 4, 7, 2, 1],
    ![1, 2, 7, 4, 6, 5, 0, 3],
    ![7, 4, 1, 2, 0, 3, 6, 5],
    ![5, 6, 3, 0, 2, 1, 4, 7] ],
  ![![0, 4, 3, 7, 6, 2, 5, 1],
    ![5, 1, 6, 2, 3, 7, 0, 4],
    ![1, 5, 2, 6, 7, 3, 4, 0],
    ![4, 0, 7, 3, 2, 6, 1, 5],
    ![2, 6, 1, 5, 4, 0, 7, 3],
    ![7, 3, 4, 0, 1, 5, 2, 6],
    ![3, 7, 0, 4, 5, 1, 6, 2],
    ![6, 2, 5, 1, 0, 4, 3, 7] ],
  ![![0, 5, 1, 4, 2, 7, 3, 6],
    ![4, 1, 5, 0, 6, 3, 7, 2],
    ![3, 6, 2, 7, 1, 4, 0, 5],
    ![7, 2, 6, 3, 5, 0, 4, 1],
    ![6, 3, 7, 2, 4, 1, 5, 0],
    ![2, 7, 3, 6, 0, 5, 1, 4],
    ![5, 0, 4, 1, 7, 2, 6, 3],
    ![1, 4, 0, 5, 3, 6, 2, 7] ],
  ![![0, 6, 7, 1, 5, 3, 2, 4],
    ![7, 1, 0, 6, 2, 4, 5, 3],
    ![5, 3, 2, 4, 0, 6, 7, 1],
    ![2, 4, 5, 3, 7, 1, 0, 6],
    ![1, 7, 6, 0, 4, 2, 3, 5],
    ![6, 0, 1, 7, 3, 5, 4, 2],
    ![4, 2, 3, 5, 1, 7, 6, 0],
    ![3, 5, 4, 2, 6, 0, 1, 7] ],
  ![![0, 7, 5, 2, 1, 6, 4, 3],
    ![6, 1, 3, 4, 7, 0, 2, 5],
    ![7, 0, 2, 5, 6, 1, 3, 4],
    ![1, 6, 4, 3, 0, 7, 5, 2],
    ![5, 2, 0, 7, 4, 3, 1, 6],
    ![3, 4, 6, 1, 2, 5, 7, 0],
    ![2, 5, 7, 0, 3, 4, 6, 1],
    ![4, 3, 1, 6, 5, 2, 0, 7] ] ]
theorem a8Op_eq (c x y : Fin 8) : a8Op c x y = Fin.xor8 x (Fin.gf8 c (Fin.xor8 x y)) := by
  revert c x y; decide

/-- On `Fin 8`, a magma admitting every translation of `GF(8)` and multiplication by `X` — hence
all of `AGL(1, 8)` — is affine over `GF(8)`.

The translations make `x ◇ y` depend only on `x` and `y - x`, and multiplication by `X` generates
`GF(8)ˣ`, so the first row `t ↦ 0 ◇ t` is `GF(8)`-linear along the orbit
`1 → 2 → 4 → 3 → 6 → 7 → 5 → 1` and is therefore determined by `c = 0 ◇ 1`. -/
theorem op_eq_a8Op {M : Magma (Fin 8)} (h₁ : M.IsEndo (Fin.xor8 1)) (h₂ : M.IsEndo (Fin.xor8 2))
    (h₄ : M.IsEndo (Fin.xor8 4)) (hd : M.IsEndo ⇑Fin.double8) : M.op = a8Op (M.op 0 1) := by
  have h₃ : M.IsEndo (Fin.xor8 3) := by
    rw [show Fin.xor8 3 = Fin.xor8 1 ∘ Fin.xor8 2 by funext z; revert z; decide]
    exact h₁.comp h₂
  have h₅ : M.IsEndo (Fin.xor8 5) := by
    rw [show Fin.xor8 5 = Fin.xor8 1 ∘ Fin.xor8 4 by funext z; revert z; decide]
    exact h₁.comp h₄
  have h₆ : M.IsEndo (Fin.xor8 6) := by
    rw [show Fin.xor8 6 = Fin.xor8 2 ∘ Fin.xor8 4 by funext z; revert z; decide]
    exact h₂.comp h₄
  have h₇ : M.IsEndo (Fin.xor8 7) := by
    rw [show Fin.xor8 7 = Fin.xor8 1 ∘ Fin.xor8 6 by funext z; revert z; decide]
    exact h₁.comp h₆
  have hstep : ∀ t : Fin 8, M.op 0 (Fin.gf8 2 t) = Fin.gf8 2 (M.op 0 t) := fun t ↦ by
    have h := hd 0 t
    simp only [Fin.double8_apply, show Fin.gf8 2 0 = (0 : Fin 8) from rfl] at h
    exact h.symm
  have hz : M.op 0 0 = 0 := by
    have h := hstep 0
    rw [show Fin.gf8 2 0 = (0 : Fin 8) from rfl] at h
    revert h
    generalize M.op 0 0 = a
    revert a
    decide
  have e2 : M.op 0 2 = Fin.gf8 (M.op 0 1) 2 := by
    have h := hstep 1
    rw [show Fin.gf8 2 1 = (2 : Fin 8) from rfl] at h
    rw [h]; generalize M.op 0 1 = c; revert c; decide
  have e4 : M.op 0 4 = Fin.gf8 (M.op 0 1) 4 := by
    have h := hstep 2
    rw [show Fin.gf8 2 2 = (4 : Fin 8) from rfl, e2] at h
    rw [h]; generalize M.op 0 1 = c; revert c; decide
  have e3 : M.op 0 3 = Fin.gf8 (M.op 0 1) 3 := by
    have h := hstep 4
    rw [show Fin.gf8 2 4 = (3 : Fin 8) from rfl, e4] at h
    rw [h]; generalize M.op 0 1 = c; revert c; decide
  have e6 : M.op 0 6 = Fin.gf8 (M.op 0 1) 6 := by
    have h := hstep 3
    rw [show Fin.gf8 2 3 = (6 : Fin 8) from rfl, e3] at h
    rw [h]; generalize M.op 0 1 = c; revert c; decide
  have e7 : M.op 0 7 = Fin.gf8 (M.op 0 1) 7 := by
    have h := hstep 6
    rw [show Fin.gf8 2 6 = (7 : Fin 8) from rfl, e6] at h
    rw [h]; generalize M.op 0 1 = c; revert c; decide
  have e5 : M.op 0 5 = Fin.gf8 (M.op 0 1) 5 := by
    have h := hstep 7
    rw [show Fin.gf8 2 7 = (5 : Fin 8) from rfl, e7] at h
    rw [h]; generalize M.op 0 1 = c; revert c; decide
  have h₀ : M.IsEndo (Fin.xor8 0) := by
    rw [show Fin.xor8 0 = id by funext z; revert z; decide]
    intro x y; rfl
  have hrow : ∀ t : Fin 8, M.op 0 t = Fin.gf8 (M.op 0 1) t := by
    intro t
    fin_cases t
    exacts [hz.trans (Fin.gf8_zero_right _).symm, (Fin.gf8_one_right _).symm,
      e2, e3, e4, e5, e6, e7]
  have step : ∀ a : Fin 8, M.IsEndo (Fin.xor8 a) → ∀ y : Fin 8,
      M.op (Fin.xor8 a 0) y = Fin.xor8 a (M.op 0 (Fin.xor8 a y)) := fun a ha y ↦ by
    have h := ha 0 (Fin.xor8 a y)
    rw [Fin.xor8_self] at h
    exact h.symm
  have key : ∀ x y : Fin 8, M.op x y = Fin.xor8 x (M.op 0 (Fin.xor8 x y)) := by
    intro x y
    fin_cases x
    exacts [step 0 h₀ y, step 1 h₁ y, step 2 h₂ y, step 3 h₃ y,
      step 4 h₄ y, step 5 h₅ y, step 6 h₆ y, step 7 h₇ y]
  funext x y
  rw [key x y, a8Op_eq]
  exact congrArg _ (hrow _)

/-- The `81` operations on `Fin 3` admitting the reflection `x ↦ -x` — which is the transposition
of `1` and `2` — as an automorphism, parametrized by `a = 0 ◇ 1`, `b = 1 ◇ 0`, `c = 1 ◇ 1` and
`d = 1 ◇ 2`. See `Magma.op_eq_reflOp3`. -/
def reflOp3 (a b c d : Fin 3) : Fin 3 → Fin 3 → Fin 3
  | 0, 0 => 0
  | 0, 1 => a
  | 0, 2 => -a
  | 1, 0 => b
  | 1, 1 => c
  | 1, 2 => d
  | 2, 0 => -b
  | 2, 1 => -d
  | 2, 2 => -c

/-- Every magma on `Fin 3` admitting the reflection as an automorphism is one of the `81` magmas
`Magma.reflOp3 a b c d`. The four remaining entries of the table are unconstrained; the fifth,
`0 ◇ 0`, is forced to be `0`, since it is its own negative. -/
theorem op_eq_reflOp3 {M : Magma (Fin 3)} (h : M.IsEndo (fun x ↦ -x)) :
    M.op = reflOp3 (M.op 0 1) (M.op 1 0) (M.op 1 1) (M.op 1 2) := by
  have hz : M.op 0 0 = 0 := by
    have h00 := h 0 0
    simp only [neg_zero] at h00
    revert h00
    generalize M.op 0 0 = a
    revert a
    decide
  funext x y
  fin_cases x <;> fin_cases y
  · exact hz
  · rfl
  · exact (h 0 1).symm
  · rfl
  · rfl
  · rfl
  · exact (h 1 0).symm
  · exact (h 1 2).symm
  · exact (h 1 1).symm

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- If `L'` has a model on `Fin n` admitting the cyclic shift as an automorphism, then any law
definable from `L'` has a model of the special shape `x ◇ y = g (y - x) + x`. -/
theorem exists_cyclic_model_of_definableFrom {n : ℕ} [NeZero n] (M : Magma (Fin n))
    (hM : satisfies (Fin n) L') (hcyc : M.IsEndo ⇑(Equiv.addRight (1 : Fin n)))
    (h : L.DefinableFrom L') :
    ∃ g : Fin n → Fin n, @satisfies _ (Fin n) (Magma.mk fun x y ↦ g (y - x) + x) L := by
  obtain ⟨M', hM', hd⟩ := h M hM
  have he : M'.IsEndo (· + 1) := hcyc.of_definable hd
  refine ⟨fun t ↦ M'.op 0 t, ?_⟩
  have key : (Magma.mk fun x y ↦ M'.op 0 (y - x) + x) = M' := by
    have hop : (fun x y ↦ M'.op 0 (y - x) + x) = M'.op :=
      funext fun x ↦ funext fun y ↦ (Magma.op_eq_of_isEndo_add_one he x y).symm
    rw [hop]
  show @satisfies β (Fin n) (Magma.mk fun x y ↦ M'.op 0 (y - x) + x) L
  rw [key]
  exact hM'

/-- `Law.MagmaLaw.exists_cyclic_model_of_definableFrom` on `Fin 3`, with the first row spelled out
as three elements so that the conclusion can be refuted by `decide`. -/
theorem exists_cyclic3_model_of_definableFrom (M : Magma (Fin 3)) (hM : satisfies (Fin 3) L')
    (hcyc : M.IsEndo ⇑(Equiv.addRight (1 : Fin 3))) (h : L.DefinableFrom L') :
    ∃ a b c : Fin 3, @satisfies _ (Fin 3) (Magma.mk fun x y ↦ ![a, b, c] (y - x) + x) L := by
  obtain ⟨g, hg⟩ := exists_cyclic_model_of_definableFrom M hM hcyc h
  refine ⟨g 0, g 1, g 2, ?_⟩
  rw [show ![g 0, g 1, g 2] = g by funext i; fin_cases i <;> rfl]
  exact hg

/-- `Law.MagmaLaw.exists_cyclic_model_of_definableFrom` on `Fin 4`, with the first row spelled out
as four elements so that the conclusion can be refuted by `decide`. -/
theorem exists_cyclic4_model_of_definableFrom (M : Magma (Fin 4)) (hM : satisfies (Fin 4) L')
    (hcyc : M.IsEndo ⇑(Equiv.addRight (1 : Fin 4))) (h : L.DefinableFrom L') :
    ∃ a b c d : Fin 4, @satisfies _ (Fin 4) (Magma.mk fun x y ↦ ![a, b, c, d] (y - x) + x) L := by
  obtain ⟨g, hg⟩ := exists_cyclic_model_of_definableFrom M hM hcyc h
  refine ⟨g 0, g 1, g 2, g 3, ?_⟩
  rw [show ![g 0, g 1, g 2, g 3] = g by funext i; fin_cases i <;> rfl]
  exact hg

/-- If `L'` has a model on `Fin 3` with the full symmetric group as automorphisms — equivalently,
with both the cyclic shift and the reflection — then any law definable from `L'` is satisfied by
one of the three affine magmas `x ◇ y = c * (y - x) + x`. -/
theorem exists_affine3_model_of_definableFrom (M : Magma (Fin 3)) (hM : satisfies (Fin 3) L')
    (hcyc : M.IsEndo ⇑(Equiv.addRight (1 : Fin 3))) (hneg : M.IsEndo ⇑(Equiv.neg (Fin 3)))
    (h : L.DefinableFrom L') :
    ∃ c : Fin 3, @satisfies _ (Fin 3) (Magma.mk fun x y ↦ c * (y - x) + x) L := by
  obtain ⟨M', hM', hd⟩ := h M hM
  refine ⟨M'.op 0 1, ?_⟩
  have key : (Magma.mk fun x y ↦ M'.op 0 1 * (y - x) + x) = M' := by
    have hop : (fun x y ↦ M'.op 0 1 * (y - x) + x) = M'.op :=
      funext fun x ↦ funext fun y ↦
        (Magma.op_eq_of_isEndo_add_one_neg (hcyc.of_definable hd) (hneg.of_definable hd) x y).symm
    rw [hop]
  rw [key]
  exact hM'

/-- If `L'` has a model on `Fin 5` with all of `F₂₀ = AGL(1, 5)` as automorphisms — equivalently,
with both the cyclic shift and doubling — then any law definable from `L'` is satisfied by one of
the five affine magmas `x ◇ y = c * (y - x) + x`. -/
theorem exists_affine5_model_of_definableFrom (M : Magma (Fin 5)) (hM : satisfies (Fin 5) L')
    (hcyc : M.IsEndo ⇑(Equiv.addRight (1 : Fin 5))) (hdbl : M.IsEndo ⇑Fin.double5)
    (h : L.DefinableFrom L') :
    ∃ c : Fin 5, @satisfies _ (Fin 5) (Magma.mk fun x y ↦ c * (y - x) + x) L := by
  obtain ⟨M', hM', hd⟩ := h M hM
  refine ⟨M'.op 0 1, ?_⟩
  have key : (Magma.mk fun x y ↦ M'.op 0 1 * (y - x) + x) = M' := by
    have hop : (fun x y ↦ M'.op 0 1 * (y - x) + x) = M'.op :=
      funext fun x ↦ funext fun y ↦ (Magma.op_eq_of_isEndo_add_one_double
        (hcyc.of_definable hd) (hdbl.of_definable hd) x y).symm
    rw [hop]
  rw [key]
  exact hM'

/-- If `L'` has a model on `Fin 7` with all of `F₄₂ = AGL(1, 7)` as automorphisms — equivalently,
with both the cyclic shift and tripling — then any law definable from `L'` is satisfied by one of
the seven affine magmas `x ◇ y = c * (y - x) + x`. -/
theorem exists_affine7_model_of_definableFrom (M : Magma (Fin 7)) (hM : satisfies (Fin 7) L')
    (hcyc : M.IsEndo ⇑(Equiv.addRight (1 : Fin 7))) (htpl : M.IsEndo ⇑Fin.triple7)
    (h : L.DefinableFrom L') :
    ∃ c : Fin 7, @satisfies _ (Fin 7) (Magma.mk fun x y ↦ c * (y - x) + x) L := by
  obtain ⟨M', hM', hd⟩ := h M hM
  refine ⟨M'.op 0 1, ?_⟩
  have key : (Magma.mk fun x y ↦ M'.op 0 1 * (y - x) + x) = M' := by
    have hop : (fun x y ↦ M'.op 0 1 * (y - x) + x) = M'.op :=
      funext fun x ↦ funext fun y ↦ (Magma.op_eq_of_isEndo_add_one_triple
        (hcyc.of_definable hd) (htpl.of_definable hd) x y).symm
    rw [hop]
  rw [key]
  exact hM'

/-- If `L'` has a model on `Fin 4` with the alternating group as automorphisms, then any law
definable from `L'` is satisfied by one of the four magmas `Magma.a4Op c`. -/
theorem exists_alt4_model_of_definableFrom (M : Magma (Fin 4)) (hM : satisfies (Fin 4) L')
    (h₁ : M.IsEndo ⇑(Fin.xorPerm4 1)) (h₂ : M.IsEndo ⇑(Fin.xorPerm4 2))
    (hr : M.IsEndo ⇑Fin.rot4) (h : L.DefinableFrom L') :
    ∃ c : Fin 4, @satisfies _ (Fin 4) (Magma.mk (Magma.a4Op c)) L := by
  obtain ⟨M', hM', hd⟩ := h M hM
  refine ⟨M'.op 0 1, ?_⟩
  have key : (Magma.mk (Magma.a4Op (M'.op 0 1))) = M' := by
    rw [← Magma.op_eq_a4Op (h₁.of_definable hd) (h₂.of_definable hd) (hr.of_definable hd)]
  rw [key]
  exact hM'

/-- If `L'` has a model on `Fin 8` admitting all of `AGL(1, 8)` as automorphisms, then any law
first-order definable from `L'` is satisfied by one of the `8` affine magmas `Magma.a8Op c`. -/
theorem exists_affine8_model_of_definableFrom (M : Magma (Fin 8)) (hM : satisfies (Fin 8) L')
    (h₁ : M.IsEndo ⇑(Fin.xorPerm8 1)) (h₂ : M.IsEndo ⇑(Fin.xorPerm8 2))
    (h₄ : M.IsEndo ⇑(Fin.xorPerm8 4)) (hdbl : M.IsEndo ⇑Fin.double8) (h : L.DefinableFrom L') :
    ∃ c : Fin 8, @satisfies _ (Fin 8) (Magma.mk (Magma.a8Op c)) L := by
  obtain ⟨M', hM', hd⟩ := h M hM
  refine ⟨M'.op 0 1, ?_⟩
  have key : (Magma.mk (Magma.a8Op (M'.op 0 1))) = M' := by
    rw [← Magma.op_eq_a8Op (h₁.of_definable hd) (h₂.of_definable hd) (h₄.of_definable hd)
      (hdbl.of_definable hd)]
  rw [key]
  exact hM'

/-- If `L'` has a model on `Fin 3` admitting the reflection as an automorphism, then any law
definable from `L'` is satisfied by one of the `81` magmas `Magma.reflOp3 a b c d`. -/
theorem exists_reflective3_model_of_definableFrom (M : Magma (Fin 3)) (hM : satisfies (Fin 3) L')
    (hneg : M.IsEndo ⇑(Equiv.neg (Fin 3))) (h : L.DefinableFrom L') :
    ∃ a b c d : Fin 3, @satisfies _ (Fin 3) (Magma.mk (Magma.reflOp3 a b c d)) L := by
  obtain ⟨M', hM', hd⟩ := h M hM
  refine ⟨M'.op 0 1, M'.op 1 0, M'.op 1 1, M'.op 1 2, ?_⟩
  rw [← Magma.op_eq_reflOp3 (hneg.of_definable hd)]
  exact hM'

end Law.MagmaLaw

/-! ### The row and column of equation 2

Equation 2, `x = y`, says that the carrier is a subsingleton and says nothing about the operation,
so `Law.MagmaLaw.definableFrom_iff_implies_of_op_irrelevant` applies to it. Together with the fact
that equation 2 implies every law, this determines its entire row and column of the definability
graph: `L` is definable from equation 2 always, and equation 2 is definable from `L'` exactly when
`L'` implies it. In particular this covers laws such as 1485 and 1486 that have no nontrivial
finite models, and which the obstructions above therefore cannot touch. -/

/-- Equation 2 is definable from `L'` if and only if `L'` implies it. -/
theorem Law2_definableFrom_iff (L' : Law.NatMagmaLaw) :
    Law2.DefinableFrom L' ↔ L'.implies Law2 :=
  Law.MagmaLaw.definableFrom_iff_implies_of_op_irrelevant fun G M₁ M₂ hM ↦
    (@Law2.models_iff G M₂).mpr ((@Law2.models_iff G M₁).mp hM)

/-- The negative half of `Law2_definableFrom_iff`: any law with a model of at least two elements
does not define equation 2. -/
theorem not_definableFrom_Law2 {L' : Law.NatMagmaLaw} (h : ¬ L'.implies Law2) :
    ¬ Law2.DefinableFrom L' := fun hd ↦ h ((Law2_definableFrom_iff L').mp hd)

/-- Every law is definable from equation 2, since equation 2 implies every law. -/
theorem definableFrom_Law2 (L : Law.NatMagmaLaw) : L.DefinableFrom Law2 :=
  definable_of_termDefinable (termDefinable_of_termStructural
    (termStructural_of_implies (Equation2_implies L)))

/-! ### Worked examples -/

/-- **Cardinality.** Equation 2, `x = y`, holds only in subsingletons, so it is not definable from
equation 1, `x = x`, which every magma satisfies. -/
theorem Equation2_not_definableFrom_Equation1 : ¬ Law2.DefinableFrom Law1 := by
  refine Law.MagmaLaw.not_definableFrom_of_no_model
    (G := Fin 2) (Magma.mk fun x _ ↦ x) (fun _ ↦ rfl) ?_
  intro M' h
  have key : (0 : Fin 2) = 1 := h fun n ↦ if n = 0 then 0 else 1
  exact absurd key (by decide)

/-- **Symmetry.** Commutativity (equation 43, `x ◇ y = y ◇ x`) is not definable from the
left-projection law (equation 4, `x = x ◇ y`). Indeed left projection on `Fin 2` admits the
nontrivial permutation as an automorphism, and by `Magma.isEndo_swap_iff` the only two-element
magmas with that automorphism ignore one of their arguments — so none of them is commutative. -/
theorem Equation43_not_definableFrom_Equation4 : ¬ Law43.DefinableFrom Law4 := by
  refine Law.MagmaLaw.not_definableFrom_of_isAuto
    (G := Fin 2) (Magma.mk fun x _ ↦ x) (fun _ ↦ rfl) (e := Fin.swap2) (by decide) ?_
  intro M' hcomm hendo
  have key : M'.op 0 1 = M'.op 1 0 := hcomm fun n ↦ if n = 0 then 0 else 1
  rcases (Magma.isEndo_swap_iff M'.op).mp hendo with h | h | h | h <;>
    rw [h] at key <;> exact absurd key (by decide)

/-- **Cardinality, mechanically.** Equation 7, `x = y ◇ z`, has no two-element model, so it is not
definable from equation 1, `x = x`. Unlike `Equation2_not_definableFrom_Equation1` this is checked
by brute force over all sixteen operations on `Fin 2`. -/
theorem Equation7_not_definableFrom_Equation1 : ¬ Law7.DefinableFrom Law1 := by
  refine Law.MagmaLaw.not_definableFrom_of_no_fin_model (n := 2) (Magma.mk fun x _ ↦ x)
    (fun _ ↦ rfl) ?_
  intro op
  simp only [Law7.models_iff]
  revert op
  decide

/-- **Cyclic symmetry.** The constant law 46, `x ◇ y = z ◇ w`, is not definable from equation 335,
`x ◇ y = y ◇ (y ◇ x)`. The latter has a model on `Fin 3` with the cyclic shift as an automorphism,
and none of the `27` cyclically symmetric magmas on `Fin 3` is constant. -/
theorem Equation46_not_definableFrom_Equation335 : ¬ Law46.DefinableFrom Law335 := by
  intro h
  letI M : Magma (Fin 3) := Magma.mk fun x y ↦ ![0, 1, 0] (y - x) + x
  obtain ⟨a, b, c, hg⟩ := Law.MagmaLaw.exists_cyclic3_model_of_definableFrom
    M (Law335.models_iff.mpr (by decide)) (by decide) h
  clear M h
  simp only [Law46.models_iff] at hg
  revert a b c hg
  decide

/-- **Reflection symmetry.** Equation 7, `x = y ◇ z`, is not definable from equation 63,
`x = y ◇ (x ◇ (x ◇ y))`. Subtraction on `Fin 3` satisfies equation 63 and admits the reflection
`x ↦ -x` as an automorphism, and none of the `81` reflective magmas satisfies equation 7. Note
that subtraction is *not* cyclically symmetric, so the previous certificate does not apply. -/
theorem Equation7_not_definableFrom_Equation63 : ¬ Law7.DefinableFrom Law63 := by
  intro h
  letI M : Magma (Fin 3) := Magma.mk fun x y ↦ y - x
  obtain ⟨a, b, c, d, hg⟩ := Law.MagmaLaw.exists_reflective3_model_of_definableFrom
    M (Law63.models_iff.mpr (by decide)) (by decide) h
  clear M h
  simp only [Law7.models_iff] at hg
  revert a b c d hg
  decide

/-- **Full symmetry.** Equation 335, `x ◇ y = y ◇ (y ◇ x)`, is not definable from commutativity.
The commutative magma `x ◇ y = 2 * (x + y)` on `Fin 3` has all of `S₃` as automorphisms, and none
of the three affine magmas satisfies equation 335. Both weaker certificates fail here: equation 335
does have cyclically symmetric and reflective models on `Fin 3`. -/
theorem Equation335_not_definableFrom_Equation43 : ¬ Law335.DefinableFrom Law43 := by
  intro h
  letI M : Magma (Fin 3) := Magma.mk fun x y ↦ 2 * (y - x) + x
  obtain ⟨c, hg⟩ := Law.MagmaLaw.exists_affine3_model_of_definableFrom
    M (Law43.models_iff.mpr (by decide)) (by decide) (by decide) h
  clear M h
  simp only [Law335.models_iff] at hg
  revert c hg
  decide

/-- **Carrier-only laws.** Commutativity has a two-element model, so it does not imply equation 2,
and therefore does not define it either. -/
theorem Equation2_not_definableFrom_Equation43 : ¬ Law2.DefinableFrom Law43 := by
  refine not_definableFrom_Law2 fun h ↦ ?_
  letI M : Magma (Fin 2) := Magma.mk fun x y ↦ x + y
  have key := (@Law2.models_iff (Fin 2) M).mp (@h (Fin 2) M (Law43.models_iff.mpr (by decide)))
  exact absurd (key 0 1) (by decide)
