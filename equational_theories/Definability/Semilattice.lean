import equational_theories.Definability.Negative
import equational_theories.Equations.All

/-!
# The free semilattice as a definability certificate

Every symmetry certificate so far has been finite: a table on `Fin n` together with a permutation
of the carrier that happens to be an automorphism. That is forced when the target is asked only
about finite magmas, but for `DefinableFrom` -- which quantifies over *all* magmas -- a finite
model is often exactly the wrong witness, because finiteness is what creates the fixed point the
argument has to avoid.

The two heaviest cells left on the `definable`/all board, `4364 → 40` and `4541 → 40`, are of that
kind. Both sources are satisfied by every semilattice, since in a semilattice a term evaluates to
the join of the variables occurring in it and both laws have the same variables on either side.
A *finite* semilattice always has a top element, which is fixed by every automorphism, so no finite
model can refute anything here. The free semilattice does not: on the nonempty finite sets of
integers under union, translation by one is an automorphism with no fixed point, because a nonempty
finite set has a largest element and translation moves it.

The target side needs nothing but the shape of equation `40`, `x ◇ x = y ◇ y`: it says every square
is the same element `c`, and `c` is then fixed by any endomorphism, since `f c = f (a ◇ a) =
f a ◇ f a = c`. So a single fixed-point-free automorphism of the source refutes it.

Both results are automorphism arguments, so they refute first-order definability and hence
term-definability, over all magmas. They say nothing about the finite flavour, which is open for a
reason -- see `Definability/CaseSplit.lean` for the positive side of equation `40`.
-/

open Law Law.MagmaLaw

namespace Magma

/-- The nonempty finite sets of integers: the carrier of the free semilattice on `ℤ`. -/
abbrev NEFinsetInt : Type := {s : Finset ℤ // s.Nonempty}

/-- The free semilattice on `ℤ`: nonempty finite sets of integers under union. -/
@[implicit_reducible]
def unionMagma : Magma NEFinsetInt :=
  ⟨fun A B ↦ ⟨A.1 ∪ B.1, by
    obtain ⟨a, ha⟩ := A.2
    exact ⟨a, Finset.mem_union_left _ ha⟩⟩⟩

@[simp]
theorem unionMagma_op (A B : NEFinsetInt) : (unionMagma.op A B).1 = A.1 ∪ B.1 := rfl

/-- A basepoint, so that the target argument has an element to square. -/
def zeroSet : NEFinsetInt := ⟨{0}, Finset.singleton_nonempty 0⟩

theorem unionMagma_4364 : @Equation4364 NEFinsetInt unionMagma := fun x y z ↦
  Subtype.ext (by ext a; simp; tauto)

theorem unionMagma_4541 : @Equation4541 NEFinsetInt unionMagma := fun x y z ↦
  Subtype.ext (by ext a; simp; tauto)

/-- Translation by one, as a permutation of the nonempty finite sets of integers. -/
def shift : NEFinsetInt ≃ NEFinsetInt :=
  (Equiv.addRight (1 : ℤ)).finsetCongr.subtypeEquiv fun s ↦ by
    simp [Equiv.finsetCongr_apply]

@[simp]
theorem shift_coe (A : NEFinsetInt) :
    (shift A).1 = A.1.map (Equiv.addRight (1 : ℤ)).toEmbedding := rfl

theorem unionMagma_isEndo : unionMagma.IsEndo ⇑shift := fun A B ↦
  Subtype.ext (by simp [Finset.map_union])

/-- Translation by one has no fixed point: it moves the largest element of a nonempty finite set. -/
theorem shift_ne (A : NEFinsetInt) : shift A ≠ A := by
  intro h
  have hmem : A.1.max' A.2 + 1 ∈ (shift A).1 :=
    Finset.mem_map.mpr ⟨_, A.1.max'_mem A.2, rfl⟩
  rw [h] at hmem
  have := A.1.le_max' _ hmem
  omega

/-- The target side of equation `40`: every square is the same element, so it is fixed by every
endomorphism. No invertibility and no finiteness are used. -/
theorem fixed_of_40 {G : Type} (M' : Magma G) (hM' : satisfies G Law40) {f : G → G}
    (hendo : M'.IsEndo f) (a : G) : f (M'.op a a) = M'.op a a := by
  rw [hendo]
  exact (@Law40.models_iff G M').mp hM' (f a) a

end Magma

open Magma

theorem Equation40_not_definableFrom_Equation4364 : ¬ Law40.DefinableFrom Law4364 :=
  not_definableFrom_of_isAuto unionMagma
    ((@Law4364.models_iff NEFinsetInt unionMagma).mpr unionMagma_4364)
    unionMagma_isEndo
    fun M' hM' hendo ↦ shift_ne _ (fixed_of_40 M' hM' hendo zeroSet)

theorem Equation40_not_definableFrom_Equation4541 : ¬ Law40.DefinableFrom Law4541 :=
  not_definableFrom_of_isAuto unionMagma
    ((@Law4541.models_iff NEFinsetInt unionMagma).mpr unionMagma_4541)
    unionMagma_isEndo
    fun M' hM' hendo ↦ shift_ne _ (fixed_of_40 M' hM' hendo zeroSet)
